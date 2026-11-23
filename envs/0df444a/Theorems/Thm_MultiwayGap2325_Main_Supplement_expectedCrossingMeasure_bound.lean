-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_expectedCrossingMeasure_bound
-- name    : MultiwayGap2325.Main.Supplement.expectedCrossingMeasure_bound
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:42:43.081587+00:00
-- url     : https://prove2.me/theorems/d7942dd9-c2dc-487a-99f6-c01f0bb0e579
-- title:
--   Lemma 5.6 — Expected directional crossing estimate
-- statement:
--   Let $(\Xi,\mathsf P)$ be a probability space and let $C$ be a random non-opposite cut with approximation factor $\alpha$. For every face direction $(i,j)$ and every nonnegative bounded Borel test function $\varphi$, the fiberwise crossing integral
--   $$
--   \xi\mapsto\int_{\Omega_S}\varphi\,d\mu^{C(\xi)}_{Sij}
--   $$
--   is measurable and
--   $$
--   \mathbb E_\xi\!\left[\int_{\Omega_S}\varphi\,d\mu^{C(\xi)}_{Sij}\right]
--   \le \alpha\int_{\Omega_S}\varphi(x)\,dx.
--   $$
--   The lower-integral formalization uses the zero fallback for non-genuine crossing measures; almost-sure genuineness is the separate first conclusion of Lemma 5.6.
-- source:
--   STOC 2027 submission #697, Lemma 5.6 and equation (17), pp.18–19; measurability asserted in the last paragraph of p.18.

import Definitions.Def_MultiwayGap2325_Main_Supplement_FluxJumps

open MeasureTheory Filter Set
open MultiwayGap2325.Main MultiwayGap2325.Main.Supplement
open scoped BigOperators ENNReal
universe u

/-- Lemma 5.6, equation (17), with the measurability assertion from p.18. -/
theorem MultiwayGap2325.Main.Supplement.expectedCrossingMeasure_bound
    (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1)
    (Ξ : Type u) [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (C : RandomNonOppositeCut q Ξ P) (α : ℝ) (hα : HasApproximationFactor C α)
    (S : Face q) (ij : Fin q × Fin q) (hij : ij ∈ directions S)
    (φ : Vec q → ℝ) (hφ : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφbound : ∃ M : ℝ, ∀ x, |φ x| ≤ M) :
    Measurable (fun ξ => ∫⁻ x, ENNReal.ofReal (φ x)
      ∂crossingMeasure T S ij.1 ij.2 (fun x => C.labeling (ξ, x))) ∧
    (∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (φ x)
      ∂crossingMeasure T S ij.1 ij.2 (fun x => C.labeling (ξ, x)) ∂P) ≤
      ENNReal.ofReal α * ∫⁻ x, ENNReal.ofReal (φ x) ∂faceVolume T S := by sorry
