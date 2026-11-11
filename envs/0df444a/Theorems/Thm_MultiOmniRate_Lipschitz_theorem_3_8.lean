-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_theorem_3_8
-- name    : MultiOmniRate.Lipschitz.theorem_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:24:32.371255+00:00
-- url     : https://prove2.me/theorems/a7075c29-9cba-4800-b8ed-c97d5d36ca1f
-- title:
--   Theorem 3.8 — Algorithm 1: $\mathbb E[\mathrm{DecOI}_{L_{\mathrm{All}}}+\mathrm{HypOI}]\le C_K(\mathrm{Reg}_{\mathrm{dec}}+\mathrm{Reg}_{\Delta L\circ H})/n+4r$
-- statement:
--   Fix $K\ge2$, a bounded loss class $\mathcal L$ (measurable, with measurable best responses), a nonempty class $\mathcal H$ of measurable benchmark rules, $0<r\le1/2$ and a horizon $n\ge1$. Suppose the learner for $\Delta\mathcal L\circ\mathcal H$ has the expected-regret guarantee of Definition 3.6 with bound $\mathrm{Reg}_{\Delta\mathcal L\circ\mathcal H}(n)$. Then for every distribution $\mathcal D$, Algorithm 1, run with the decision learner of Algorithm 3, uses $n$ independent examples from $\mathcal D$ and returns a predictor $p$ with
--   $$\mathbb E\big[\mathrm{DecOI}_{\mathcal L_{\mathrm{All}}}(p)+\mathrm{HypOI}_{\mathcal L,\mathcal H}(p)\big]\le C_K\,\frac{\mathrm{Reg}_{\mathrm{dec}}(n,r)+\mathrm{Reg}_{\Delta\mathcal L\circ\mathcal H}(n)}{n}+4r,$$
--   where $\mathrm{Reg}_{\mathrm{dec}}(n,r)=C'_Knr+C'_K\sqrt n\,f_K(r)$ is the decision-learner bound (3.4), the expectation is over the sample $S\sim\mathcal D^n$ and the hypothesis learner's randomness, and $C_K,C'_K$ depend only on $K$. By Theorem 2.2 the same bound holds for $\mathbb E[\mathrm{OmniReg}_{\mathcal L,\mathcal H}(p)]$.
--
--   This population guarantee converts the online regret bounds into omniprediction, by sequential symmetrization.
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - encoding: randomized predictor $\mathcal X\to\Delta(\Delta_K)$; modeled label $\tilde y\sim p(x)$ → Markov kernel `Kernel X (Simplex K)`; $\mathbb E_{\tilde y\sim a}\ell(\cdot,\tilde y)$ written as $\langle a,\ell(\cdot,\cdot)\rangle$; reason: footnote 3 (p. 19); the modeled-label expectation is exact
--   - reading: "we fix a measurable best response" (p. 19); benchmark rules $h$ → each $\ell\in\mathcal L$ is measurable in the action with measurable $\mathrm{BR}_\ell$ (`BRLoss.IsMeasurable`), each $h\in\mathcal H$ is measurable; reason: the paper's standing convention; it is what makes every expectation defined
--   - generalization: Algorithm 3 with covers obeying "the size bounds of Lemma 3.11" (its constant) → admissible covers (`Alg3Covers`) with Lemma 3.11's bound for every constant $C_{\mathrm{cov}}>0$; $C_K,C'_K$ are chosen after $C_{\mathrm{cov}}$; reason: Lemma 3.11's constant is one admissible $C_{\mathrm{cov}}$
--   - reading: "$\mathrm{Reg}_{\mathrm{dec}}$ is the decision-learner bound in (3.4)" → $C_2nr+C_2\sqrt n\,f_K(r)$ with its own existential constant $C_2$ (depending on $K$, $C_{\mathrm{cov}}$), next to $C_1=C_K$; reason: (3.4) carries an existential $C_K$
--   - reading: hypothesis learner of Definition 3.6(2): tests $g_t:\mathcal X\to[-5,5]^K$, every adaptive sequence, expectation over its randomness → `HypLearner`: tests measurable in $x$; adversaries see the history and every test revealed so far; the expectation as an upper integral (`HypGuarantee`); reason: measurability makes the population expectations and the output predictor defined; for measurable integrands the upper integral is the expectation
--   - reading: "by a fixed choice of minimizer" (Algorithm 1, step 5) → any `MinSelector`: a minimizer for every continuous $w$, measurable in $g_t(x)$; reason: measurable selections of the minimizer exist (continuous objective on a compact set); measurability makes $\mathrm{Predict}$ a randomized predictor
--   - encoding: $\mathbb E$ over $S\sim\mathcal D^n$ and the learner's randomness; "By Theorem 2.2, the same bound holds for $\mathbb E[\mathrm{OmniReg}]$" → `UpperExpLE` under $\mathcal D^n\otimes P$, for $\mathrm{DecOI}_{\mathcal L_{\mathrm{All}}}+\mathrm{HypOI}$ and, as a second conjunct, for OmniReg; reason: the map $(S,\omega)\mapsto$ error need not be measurable; the upper integral is the expectation when it is
--   - encoding: $\mathcal L_{\mathrm{All}}$: arbitrary action spaces → `AllLoss.{u} K`: action spaces in a universe `u`, with a measurable structure; reason: $w_{\ell,r}$ and the Decision-OI term depend on $\ell$ only through $\ell^{\mathrm{pr}}$, which is itself a loss on $\Delta_K$, so every universe gives the same class
--   - encoding: rounds $t=1,\dots,n$; $\tau\sim\mathrm{Unif}\{1,\dots,n\}$ → rounds $t=0,\dots,n-1$; $\tau$ uniform on `Fin n` (`unifFin n`); reason: index shift only
--   - encoding: $\mathrm{Unif}(\Delta_K)$ → `unifSimplex K`: normalized Lebesgue measure on the free coordinates $(p_1,\dots,p_{K-1})$, pushed to $\Delta_K$; reason: the uniform distribution on the simplex, as in the proof of Lemma 3.3 (App. A.1)
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 28, Theorem 3.8 (proof: pp. 59–62, App. A.4)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_OmniErrors
import Definitions.Def_MultiOmniRate_Lipschitz_Smoothing
import Definitions.Def_MultiOmniRate_Lipschitz_Learners

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem theorem_3_8.{u, v, w, z} : ∀ (K : ℕ) [NeZero K], 2 ≤ K → ∀ (Ccov : ℝ), 0 < Ccov →
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
    ∀ (X : Type u) [MeasurableSpace X] (A : Type v) [MeasurableSpace A]
      (L : Set (BRLoss K A)), (∀ ℓ ∈ L, ℓ.IsMeasurable) →
    ∀ (H : Set (X → A)), (∀ h ∈ H, Measurable h) → H.Nonempty →
    ∀ (r : ℝ), 0 < r → r ≤ 1 / 2 → ∀ (n : ℕ), 1 ≤ n →
    ∀ (Ω : Type w) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Hyp : HypLearner K X Ω) (Reg : ℝ), HypGuarantee (testClass L H) Hyp P n Reg →
    ∀ (σ : MinSelector K) (B : ℕ → Finset (Simplex K → Fin K → ℝ)), Alg3Covers.{z} K r Ccov B →
    ∀ (D : Measure (X × Fin K)) [IsProbabilityMeasure D],
      UpperExpLE ((Measure.pi fun _ : Fin n => D).prod P)
        (fun Sω => DecOIAll.{z} D (alg1 B n r σ Hyp Sω.2 Sω.1) +
          HypOI L H D (alg1 B n r σ Hyp Sω.2 Sω.1))
        (C₁ * ((C₂ * n * r + C₂ * Real.sqrt n * fK K r) + Reg) / n + 4 * r) ∧
      UpperExpLE ((Measure.pi fun _ : Fin n => D).prod P)
        (fun Sω => OmniReg L H D (alg1 B n r σ Hyp Sω.2 Sω.1))
        (C₁ * ((C₂ * n * r + C₂ * Real.sqrt n * fK K r) + Reg) / n + 4 * r) := by sorry

end MultiOmniRate.Lipschitz
