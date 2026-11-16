-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_K_2
-- name    : MetricMinTest.Supplement.theorem_K_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:52:41.001208+00:00
-- url     : https://prove2.me/theorems/a8f9a119-986b-43a3-9b81-55307dcfb121
-- title:
--   Theorem K.2, p.32 — tests from a fractional certificate cover: expected cost $400C(y)L$, budget $3200C(y)L$, also with $F_{\mathcal C}$
-- statement:
--   Let $\mathcal P$ be an instance class with disjoint nonempty subsets $\mathcal P^+$, $\mathcal P^-$ and a finite nonempty certificate family $\mathcal C$: querying $c$ returns a fresh $X_c\in[-1,1]$ with mean $m_c(P)$. Known thresholds $a_c\in[-1,1]$ and gaps $\eta_c\in(0,2]$ satisfy $m_c(P)\ge a_c+\eta_c$ on $\mathcal P^+$. Let $y$ be a fractional certificate cover ($y\ge0$, $\sum_{c:m_c(P)\le a_c}y_c\ge1$ for every $P\in\mathcal P^-$) with cost $C(y)=\sum_cy_c\eta_c^{-2}$, and $\delta\in(0,1/4]$. Then
--
--   1. a tester stops on all instances, has both errors at most $\delta$ (accepting $P\in\mathcal P^-$ and rejecting $P\in\mathcal P^+$), and satisfies $\sup_{P\in\mathcal P^+}\mathbb E_P\tau\le400\,C(y)\ln(1/\delta)$;
--   2. another such tester has deterministic budget $3200\,C(y)\ln(1/\delta)$.
--
--   Both conclusions hold with the optimal cover cost $F_{\mathcal C}$ in place of $C(y)$.
--
--   The randomized-certificate argument thus applies to any system of threshold statements in which every violation falsifies a weighted certificate, metric or not.
--
--   **Formalization Note** The class is a type $X$ mapped to instances indexed by the certificates; testers query certificates.
--
--   Differences from the source:
--   - encoding: an instance class with certificate means → a type $X$ with $x\mapsto$ an instance (laws on $[-1,1]$) indexed by the certificate family, observed through the stack-of-streams model; reason: querying $c$ returns fresh independent observations of law $P_c$
--   - encoding: both errors at most $\delta$ → validity on (range of the class, image of $\mathcal P^-$, image of $\mathcal P^+$) at level $\delta$, including almost-sure stopping and measurability; reason: the contract of Definition 2.1 for this system
--   - reading: stops on all instances → almost-sure stopping on every instance of the class and, in addition, a finite stopping time for every private draw and every observation table; reason: the strongest reading
--   - encoding: $y$ has finite cost → $y$ real-valued; reason: real costs are finite
--   - reading: both conclusions hold with $F_{\mathcal C}$ → if some fractional certificate cover exists, both testers exist with $F_{\mathcal C}$ in place of $C(y)$; reason: $F_{\mathcal C}$ is the optimum of the cover program, defined (and attained) when it is feasible (p.32)
--   - encoding: expectations and probabilities → over private randomness times the observation table, in $[0,\infty]$; reason: published tester model
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition K.1 and Theorem K.2, p.32

import Mathlib
import Definitions.Def_MetricMinTest_Supplement_IsValidOn
import Definitions.Def_MetricMinTest_Supplement_IsCertCover
import Definitions.Def_MetricMinTest_Supplement_certCoverCost
import Definitions.Def_MetricMinTest_Supplement_certCoverOpt

namespace MetricMinTest.Supplement

open MeasureTheory

/-- **Theorem K.2 (Tests from a fractional certificate cover).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition K.1 and
Theorem K.2, p.32: "An instance class P has disjoint subsets P+ and P− and a finite nonempty
certificate family C. Querying c returns a fresh X_c ∈ [−1, 1] with mean m_c(P), conditionally
independent of the past. Known thresholds a_c ∈ [−1, 1] and gaps η_c ∈ (0, 2] satisfy
m_c(P) ≥ a_c + η_c on P+. … Theorem K.2. Assume P+, P− are nonempty and y has finite cost. For
δ ∈ (0, 1/4], a tester stops on all instances, has both errors at most δ, and satisfies
sup_{P∈P+} E_P τ ≤ 400 C(y) ln(1/δ). Another has deterministic budget 3200 C(y) ln(1/δ). Both
conclusions hold with F_C."

**Formalization Note.** The class is a type `X` with `inst x : Instance C` the laws of the
certificates (laws on `[−1, 1]`, queried through the stack-of-streams model); a tester queries
certificates. "Both errors at most δ" and stopping a.s. are `IsValidOn` with class `range inst`,
`neg = inst '' P−`, `pos = inst '' P+`; "stops on all instances" is in addition a finite stopping
time for every private draw and every observation table. A deterministic budget holds for every
draw and table. `y` is any fractional certificate cover (its cost is a real number). The `F_C`
version is stated under the hypothesis that some fractional certificate cover exists, where the
paper's optimum `F_C` is defined (attained, p.32). -/
theorem theorem_K_2 {C X : Type} [Fintype C] [Nonempty C] [DecidableEq C]
    (inst : X → Instance C) (Ppos Pneg : Set X) (hpos : Ppos.Nonempty) (hneg : Pneg.Nonempty)
    (hdisj : Disjoint Ppos Pneg) (a η : C → ℝ) (ha : ∀ c, a c ∈ Set.Icc (-1 : ℝ) 1)
    (hη : ∀ c, η c ∈ Set.Ioc (0 : ℝ) 2) (hgap : ∀ x ∈ Ppos, ∀ c, a c + η c ≤ (inst x).mean c)
    (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) (1 / 4)) :
    (∀ y : C → ℝ, IsCertCover inst Pneg a y →
      (∃ T : Tester C, IsValidOn T (Set.range inst) (inst '' Pneg) (inst '' Ppos) δ ∧
        (∀ ξ ω, T.stopTime ξ ω ≠ ⊤) ∧
        (⨆ (x : X) (_ : x ∈ Ppos),
          ∫⁻ p, ((T.stopTime p.1 p.2 : ℕ∞) : ENNReal) ∂(T.μξ.prod (streamLaw (inst x)))) ≤
          ENNReal.ofReal (400 * certCoverCost η y * Real.log (1 / δ))) ∧
      (∃ T : Tester C, IsValidOn T (Set.range inst) (inst '' Pneg) (inst '' Ppos) δ ∧
        ∀ ξ ω, ((T.stopTime ξ ω : ℕ∞) : ENNReal) ≤
          ENNReal.ofReal (3200 * certCoverCost η y * Real.log (1 / δ)))) ∧
    ((∃ y : C → ℝ, IsCertCover inst Pneg a y) →
      (∃ T : Tester C, IsValidOn T (Set.range inst) (inst '' Pneg) (inst '' Ppos) δ ∧
        (∀ ξ ω, T.stopTime ξ ω ≠ ⊤) ∧
        (⨆ (x : X) (_ : x ∈ Ppos),
          ∫⁻ p, ((T.stopTime p.1 p.2 : ℕ∞) : ENNReal) ∂(T.μξ.prod (streamLaw (inst x)))) ≤
          ENNReal.ofReal (400 * certCoverOpt inst Pneg a η * Real.log (1 / δ))) ∧
      (∃ T : Tester C, IsValidOn T (Set.range inst) (inst '' Pneg) (inst '' Ppos) δ ∧
        ∀ ξ ω, ((T.stopTime ξ ω : ℕ∞) : ENNReal) ≤
          ENNReal.ofReal (3200 * certCoverOpt inst Pneg a η * Real.log (1 / δ)))) := by sorry

end MetricMinTest.Supplement
