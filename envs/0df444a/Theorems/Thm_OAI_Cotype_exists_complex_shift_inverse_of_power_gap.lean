-- Prove2me | Theorems.Thm_OAI_Cotype_exists_complex_shift_inverse_of_power_gap
-- name    : OAI.Cotype.exists_complex_shift_inverse_of_power_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:01:49.360557+00:00
-- url     : https://prove2.me/theorems/373cba90-dc5f-4cf1-8700-1026f619bc17
-- title:
--   Inverting complex shifts of a contraction with a power gap
-- statement:
--   Let $\mathcal A$ be a complex Banach algebra with $\|1\|=1$, $N\in\mathbb N$, $C\ge0$, $\rho>0$ with $C<\rho^N$. Let $S\in\mathcal A$ satisfy $\|S\|\le1$ and $\|(1-S)^N\|\le C$, and let $\beta\in\mathbb C$ with $|\beta|\ge\rho$. Then $(\beta-1)+S$ is invertible and
--   $$
--   \bigl\|\bigl((\beta-1)+S\bigr)^{-1}\bigr\|\le\frac{\Phi_N(2/\rho,\,C/\rho^N)}{|\beta|},
--   $$
--   where $\Phi_N(b,q)=\bigl(\sum_{k<N}b^k\bigr)/(1-q)$.
--
--   So a power gap for $1-S$ keeps the spectrum of $S$ away from $1-\beta$ for all large shifts $\beta$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ComplexPowerGapInverse.lean#L11-L58

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse

open OAI OAI.Cotype

theorem OAI.Cotype.exists_complex_shift_inverse_of_power_gap {N : ℕ} {C ρ : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hgap : C < ρ^N)
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A] [CompleteSpace A]
    (T : A) (hT : ‖T‖ ≤ 1) (hTN : ‖(1-T)^N‖ ≤ C)
    (β : ℂ) (hβ : ρ ≤ ‖β‖) :
    ∃ U : Aˣ, (U : A) = (β-1) • (1 : A) + T ∧
      ‖(↑U⁻¹ : A)‖ ≤ powerGapInverseBound N (2/ρ) (C/ρ^N) / ‖β‖ := by sorry
