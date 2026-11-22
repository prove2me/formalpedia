-- Prove2me | Theorems.Thm_MasulloRH_unit_height_zeta_right_rectangle_mesh_certificates
-- name    : MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates
-- status  : Open
-- author  : @GeorgeCoote
-- created : 2026-11-21T18:13:13.223871+00:00
-- url     : https://prove2.me/theorems/f9f6d44b-a148-4b98-8aa0-a911a4eaa8b4
-- title:
--   Open rational-mesh certificates for nonvanishing in right-hand unit-band rectangles
-- statement:
--   For natural numbers $n,k$, set $L=100000+n$, $H=L+1$, and $d=1/(k+3)$. Consider the closed rectangle
--   $$
--   R_{n,k}=[1/2+d,1]\times[L+d,H]\subset\mathbb C.
--   $$
--
--   The certificate asks for a positive integer $m$ and a nonnegative rational $M$. The bound $|\zeta'(s)|\le M$ must hold throughout $R_{n,k}$. At each of the $(m+1)^2$ grid points $q$ obtained by dividing each side into $m$ equal segments, require
--   $$
--   |\zeta(q)|>\frac{2M}{m}.
--   $$
--
--   The derivative bound and the strict sample inequalities certify nonvanishing on the full rectangle. Allowing $k$ to grow exhausts the half-open unit band to the right of the critical line. The assertion that these certificates exist for all $n,k$ is open.
-- source:
--   New finite-mesh certificate condition for MasulloRH.unit_height_signed_critical_band_certificates, https://prove2.me/theorems/3df4bb7e-e781-4256-92ab-e60c3b78f185. The analytic step is the mean-value estimate Convex.norm_image_sub_le_of_norm_deriv_le in Mathlib, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/MeanValue.lean#L729.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    ∃ (m : ℕ) (M : ℚ), 0 < m ∧ 0 ≤ M ∧
      (∀ s ∈ Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top),
        ‖deriv riemannZeta s‖ ≤ (M : ℝ)) ∧
      ∀ i j : Fin (m + 1),
        let s : ℂ :=
          ⟨left + (1 - left) * ((i.val : ℝ) / m),
            bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
        2 * (M : ℝ) / m < ‖riemannZeta s‖ := by sorry
