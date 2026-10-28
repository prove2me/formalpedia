-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_norm_toLp_smul_gradient_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.norm_toLp_smul_gradient_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:37.703909+00:00
-- url     : https://prove2.me/theorems/498d247b-5ee4-41ec-a4b1-bd5e9cc8d247
-- title:
--   Caccioppoli Estimate For A Mollified Equation
-- statement:
--   This lemma is a localized gradient estimate.
--
--   Let $V$ be finite-dimensional and complete, let $m$ be an additive Haar measure, and let $\chi,v:V\to\mathbb R$ be smooth, with $\chi$ compactly supported. Let $H:V\to V$ satisfy, for every smooth compactly supported $g$ with $\operatorname{tsupp}(g)\subseteq\operatorname{tsupp}(\chi)$,
--
--   $$
--   \int (\Delta g)v\,dm
--   =\int \langle\nabla g,H\rangle\,dm+\int gv\,dm.
--   $$
--
--   If the three fields $\chi\nabla v$, $v\nabla\chi$, and $\chi H$ belong to $L^2(m)$, then
--
--   $$
--   \|\chi\nabla v\|_{L^2(m)}
--   \le
--   3\|v\nabla\chi\|_{L^2(m)}+2\|\chi H\|_{L^2(m)}.
--   $$
--
--   The estimate is stated using `MemLp.toLp` and ordinary real norms. It is a technical local bound used to show that localized gradients of mollifications are Cauchy.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem norm_toLp_smul_gradient_le {χ v : V → ℝ} (hχ : ContDiff ℝ ∞ χ)
--       (hχc : HasCompactSupport χ) (hv : ContDiff ℝ ∞ v) {H : V → V}
--       (heq : ∀ g : V → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ tsupport χ →
--         ∫ x, Laplacian.laplacian g x * v x ∂m =
--           ∫ x, ⟪gradient g x, H x⟫ ∂m + ∫ x, g x * v x ∂m)
--       (hA : MemLp (fun x => χ x • gradient v x) 2 m) (hB : MemLp (fun x => v x • gradient χ x) 2 m)
--       (hC : MemLp (fun x => χ x • H x) 2 m) :
--       ‖hA.toLp _‖ ≤ 3 * ‖hB.toLp _‖ + 2 * ‖hC.toLp _‖
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/InteriorRegularity`](https://prove2.me/theorems/79e586aa-54d4-4c9a-ac32-31116ce1ca0f).
--
--   Next: [`integral_laplacian_mul_convolution_eq`](https://prove2.me/theorems/4e49d784-08a5-433a-989e-30d5dbb063cf).
--
--   [Source excerpt, lines 143–150](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean#L143-L150) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean#L139-L236 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity`, declaration `_private.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity.0.FunctionalInequalities.KLS.LogConcave.norm_toLp_smul_gradient_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity

open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped ContDiff RealInnerProductSpace Convolution ENNReal
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.KLS.LogConcave.norm_toLp_smul_gradient_le_readable {χ v : V → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hv : ContDiff ℝ ∞ v) {H : V → V}
    (heq : ∀ g : V → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ tsupport χ →
      ∫ x, Laplacian.laplacian g x * v x ∂m =
        ∫ x, ⟪gradient g x, H x⟫ ∂m + ∫ x, g x * v x ∂m)
    (hA : MemLp (fun x => χ x • gradient v x) 2 m) (hB : MemLp (fun x => v x • gradient χ x) 2 m)
    (hC : MemLp (fun x => χ x • H x) 2 m) :
    ‖hA.toLp _‖ ≤ 3 * ‖hB.toLp _‖ + 2 * ‖hC.toLp _‖ := by sorry
