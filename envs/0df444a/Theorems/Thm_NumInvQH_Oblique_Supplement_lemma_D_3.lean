-- Prove2me | Theorems.Thm_NumInvQH_Oblique_Supplement_lemma_D_3
-- name    : NumInvQH.Oblique.Supplement.lemma_D_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:48:48.624547+00:00
-- url     : https://prove2.me/theorems/635f23ac-1d00-4d20-9b92-6614e1d63884
-- title:
--   Lemma D.3 — A two-line identity of stochastic-logarithm brackets for X, X−, L, L− > 0 and any semimartingale W̃ (Yor's formula).
-- statement:
--   Let $X,L,W$ be scalar semimartingales, with $X,X_-,L,L_->0$. Then both equalities in the following chain hold up to indistinguishability on $[0,T]$:
--   $$W+[W,\mathcal L(X^{-1})]+[W+[W,\mathcal L(X^{-1})],\mathcal L(LX^2)]
--   =W+[W,\mathcal L(LX)]
--   =W+[W,\mathcal L(X)]+[W+[W,\mathcal L(X)],\mathcal L(L)].$$
--   The brackets are actual quadratic covariations and the logarithms are actual stochastic integrals. This is the double Yor identity used in the characteristic transformations.
--
--   The initial sigma field is $P$-trivial, as in the standing setting on p. 2.
--
--   Differences from the source:
--   - encoding: finite-horizon vector processes and stochastic equality → Fin-indexed coordinates, stopped extensions and indistinguishability on [0,T]; reason: this preserves the full finite-horizon domain, including null modifications and arbitrary finite dimension d ≥ 2
--   - encoding: the general predictable vector integral of [22, III.6.17] → elementary-sum construction followed by bounded predictable extension and Emery convergence of joint truncations; reason: this constructs general vector integration and retains cancellation; it does not impose coordinatewise integrability, absolute continuity of characteristics, or calculus axioms
--   - encoding: stochastic integrals, brackets, logarithms, exponentials and conditional processes → chosen genuine versions from explicit defining relations; reason: these quantities are unique up to indistinguishability on the stated domain; their outside-domain zero defaults are not hypotheses or replacement values for source objects
--   - generalization: X is the designated coordinate of the Appendix D market, with its terminal second-moment assumptions → X is any positive scalar semimartingale with positive left limits; reason: the p. 37 proof uses only the Yor product formula and brackets of X, L and W; every Appendix D instance specializes to this domain without imposing any extra hypothesis
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 37, Lemma D.3

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Market

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NumInvQH.Oblique.Supplement

theorem lemma_D_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (h0 : ∀ A, MeasurableSet[ℱ 0] A → P A = 0 ∨ P A = 1)
    (T : ℝ≥0)
    (X L W : Process Ω ℝ) (hX : ScalarSemi P ℱ T X) (hL : ScalarSemi P ℱ T L)
    (hW : ScalarSemi P ℱ T W) (hXp : Positive P T X) (hLp : Positive P T L) :
    let log := stochasticLog P ℱ T
    let bracket := covariation P ℱ T
    let U := fun t ω => W t ω + bracket W (log (fun t ω => (X t ω)⁻¹)) t ω
    let V := fun t ω => W t ω + bracket W (log X) t ω
    Same P T (fun t ω => U t ω + bracket U (log (fun t ω => L t ω * X t ω ^ 2)) t ω)
      (fun t ω => W t ω + bracket W (log (fun t ω => L t ω * X t ω)) t ω) ∧
    Same P T (fun t ω => W t ω + bracket W (log (fun t ω => L t ω * X t ω)) t ω)
      (fun t ω => V t ω + bracket V (log L) t ω) := by sorry

end NumInvQH.Oblique.Supplement
