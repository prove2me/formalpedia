-- Prove2me | Theorems.Thm_MasulloRH_finite_high_zero_interpolating_mellin_kernels
-- name    : MasulloRH.finite_high_zero_interpolating_mellin_kernels
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:36:06.731116+00:00
-- url     : https://prove2.me/theorems/564967bd-547d-4cba-9db3-b095cab5523e
-- title:
--   Small physical convolution kernels interpolating every jet in finite high zeta clusters
-- statement:
--   For any admissible test, a finite collection of zeros above 5/2+2n can be interpolated to every multiplicity by a single physical kernel k. Its integral against exp(3|y|/2) in absolute value is O((n+1)^−4) with a constant independent of the number, spacings and multiplicities of the selected zeros.
-- source:
--   Finite support interpolation step for Masullo The Music of the Primes §10, with paired half-plane rational factors, the validated weighted zero tail, explicit causal inverses and Fourier inversion. Related close-zero gap: https://github.com/mccorvie/riemann-masullo/issues/1169.

import Definitions.Def_MasulloRH_RationalTrace
open MeasureTheory MasulloRH
open scoped Topology

theorem MasulloRH.finite_high_zero_interpolating_mellin_kernels (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) :
    ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, ∀ F : Finset (ZetaZerosInTraceStrip (1/2)),
      (∀ z∈F, (5/2:ℝ)+2*n < |z.val.im|) →
      ∃ k : ℝ→ℂ, AEStronglyMeasurable k ∧
        Integrable (fun y => ‖k y‖*Real.exp ((3/2:ℝ)*|y|)) ∧
        (∫ y : ℝ, ‖k y‖*Real.exp ((3/2:ℝ)*|y|)) ≤ K/((n:ℝ)+1)^4 ∧
        ∀ z∈F, ∀ j < analyticOrderNatAt riemannZeta z.val,
          (∫ y : ℝ, φ (Real.exp y)*(y:ℂ)^j*Complex.exp ((z.val-1/2)*y)) =
          ∫ y : ℝ, k y*(y:ℂ)^j*Complex.exp ((z.val-1/2)*y) := by sorry
