-- Prove2me | Theorems.Thm_GeoSemialgCSP_lemma_5_1
-- name    : GeoSemialgCSP.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:44.407442+00:00
-- url     : https://prove2.me/theorems/39e7d394-454b-4cfc-9beb-14b2997a63f4
-- title:
--   Lemma 5.1 — the lower coarse predicate
-- statement:
--   Assume the standing hypotheses of Section 4 (as in Lemma 4.4). For every $R$, every partition $X=S_0\sqcup\dots\sqcup S_{q-1}$ into $q\le q_0$ nonempty parts, and every fractional coarse solution $F:[M]^R\to\mathcal P_q$,
--   $$\mathrm{val}(F,(J_R)_{P^-})\ \le\ \alpha^*_P+\varepsilon ,$$
--   where $P^-(a)=\min_{x_j\in S_{a_j}}P(x_1,\dots,x_k)$ is the lower coarse predicate and $\alpha^*_P$ is taken over distributions on $X$.
--
--   Coarse solutions of the lower predicate cannot beat the biased random assignment of $P$.
--
--   Differences from the source:
--   - encoding: a predicate P : (ℝ^d)^k → {0,1}, semialgebraic in the k·d coordinates → its accepting set S ⊆ (EuclideanSpace ℝ (Fin d))^k, semialgebraic through finProdFinEquiv; reason: the same predicate; P(x) = 1 iff x ∈ S
--   - generalization: property (2): a cousins homomorphism for every finite ordered k-ary tree → HasCousinsHoms: one for every complete ordered k-ary tree; reason: a weaker hypothesis: every finite ordered k-ary tree embeds in a complete one preserving cousins tuples, so the printed property implies it; the proof uses only complete trees (Lemma 4.3 item 4)
--   - generalization: R ≥ 1 (Let R ≥ 1, p.11) → every R : ℕ; reason: the R ≥ 1 cases are included; at R = 0 the test has a single variable and the inequality also holds
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 5.1, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_IsSemialgebraicPred
import Definitions.Def_GeoSemialgCSP_HasCousinsHoms
import Definitions.Def_GeoSemialgCSP_MSSound
import Definitions.Def_GeoSemialgCSP_RE1
import Definitions.Def_GeoSemialgCSP_RE2
import Definitions.Def_GeoSemialgCSP_RE3
import Definitions.Def_GeoSemialgCSP_valJ
import Definitions.Def_GeoSemialgCSP_alphaStar
import Definitions.Def_GeoSemialgCSP_lowerPred
import Definitions.Def_GeoSemialgCSP_IsPartitionOf

namespace GeoSemialgCSP

/-- **Lemma 5.1 (the lower coarse predicate).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 5.1, printed p.14 (PDF p.15): for every
partition of `X` into `q ≤ q₀` nonempty parts and every fractional coarse solution `F`,
`val(F, (J_R)_{P⁻}) ≤ α*_P + ε`.

**Formalization Note.** The standing assumptions of §4 are hypotheses. `α*_P` is taken over
finitely supported distributions on `X`. -/
theorem lemma_5_1 {k d : ℕ} (hk : 2 ≤ k) (X : Set (E d)) (S : Set (Fin k → E d))
    (hsa : IsSemialgebraicPred S) (hcous : HasCousinsHoms X S)
    (q₀ : ℕ) (ε : ℝ) (hq₀ : 1 ≤ q₀) (hε : 0 < ε) {h H : ℕ} (hh : 1 ≤ h) (hms : MSSound k q₀ ε h)
    (L : PMF ((Fin h → Fin k) → Wd k H)) (εL : ℝ) (hεL : 0 < εL)
    (hL1 : RE1 L) (hL2 : RE2 L) (hL3 : RE3 L εL)
    (R q : ℕ) (hq : q ≤ q₀) (part : Fin q → Set (E d)) (hpart : IsPartitionOf part X)
    (F : (Fin R → Wd k H) → Fin q → ℝ) (hF : ∀ z, F z ∈ stdSimplex ℝ (Fin q)) :
    valJ L R (lowerPred S part) F ≤ alphaStar X S + ε := by sorry

end GeoSemialgCSP
