-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_finite_variation_and_expected_crossings
-- name    : MultiwayGap2325.Main.Supplement.finite_variation_and_expected_crossings
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:04:32.815099+00:00
-- url     : https://prove2.me/theorems/b27458c8-4503-4f21-9926-256099af9306
-- title:
--   Lemma 5.6 — Finite variation and expected crossings
-- statement:
--   Let $C$ be a random non-opposite cut with approximation factor $\alpha$. On one event of probability one, every face has finite directional crossing measures. For each face $S$, direction $e_i-e_j$, and bounded nonnegative Borel function $\varphi$,
--   $$
--   \mathbb E\!\left[\int \varphi\,d\mu^S_{ij}(C)\right]
--   \le \alpha\int_{\Omega_S}\varphi(x)\,dx.
--   $$
--   Consequently, for every face,
--   $$
--   \mathbb E[\operatorname{cost}_S(C)]
--   \le \alpha\sum_{i<j\in S}\int_{\Omega_S}w^S_{ij}(x)\,dx.
--   $$
--   These expected bounds also imply that fixed cell-wall null sets carry no crossing mass almost surely, which is the regularity needed by the interface and boundary arguments.
--
--   **Formalization Note** Expectations are nonnegative lower integrals. The existing zero fallback of `crossingMeasure` is harmless because genuine finite crossing measures exist almost surely; no BV or finite-perimeter regularity is added as an assumption on the cut.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Lemma 5.6 and equation (17), pp.17–19.

import Definitions.Def_MultiwayGap2325_Main_Supplement_FluxJumps

open MeasureTheory Filter Set
open MultiwayGap2325.Main MultiwayGap2325.Main.Supplement
open scoped BigOperators ENNReal
universe u

/-- Lemma 5.6, pp.17–19. The second conclusion is stated with lower integrals;
infinite-crossing realizations use the zero fallback of crossingMeasure and are
excluded by the first conclusion. -/
theorem MultiwayGap2325.Main.Supplement.finite_variation_and_expected_crossings
    (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) (D : FlowData q)
    (hD : IsFlowInstance T D)
    (Ξ : Type u) [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (C : RandomNonOppositeCut q Ξ P) (α : ℝ) (hα : HasApproximationFactor C α) :
    (∀ᵐ ξ ∂P, ∀ S : Face q,
      HasFiniteCrossings T S (fun x => C.labeling (ξ, x))) ∧
    (∀ (S : Face q) (ij : Fin q × Fin q), ij ∈ directions S →
      ∀ φ : Vec q → ℝ, Measurable φ →
        (∀ x, 0 ≤ φ x) → (∃ M : ℝ, ∀ x, |φ x| ≤ M) →
        (∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (φ x)
          ∂crossingMeasure T S ij.1 ij.2 (fun x => C.labeling (ξ, x)) ∂P) ≤
          ENNReal.ofReal α * ∫⁻ x, ENNReal.ofReal (φ x) ∂faceVolume T S) ∧
    ∀ S : Face q,
      (∫⁻ ξ, faceCost T D.weighting S (fun x => C.labeling (ξ, x)) ∂P) ≤
        ENNReal.ofReal α * ∑ ij ∈ directions S,
          ∫⁻ x, ENNReal.ofReal (D.weighting.weight S ij.1 ij.2 x) ∂faceVolume T S := by sorry
