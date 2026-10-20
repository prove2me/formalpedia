-- Prove2me | Theorems.Thm_OAI_Cotype_exists_sector_timed_shift
-- name    : OAI.Cotype.exists_sector_timed_shift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:05:14.783474+00:00
-- url     : https://prove2.me/theorems/acc2da23-bfa0-4c0c-b021-da4e5cd21168
-- title:
--   Choosing times for complex shifts in a sector
-- statement:
--   Let $1<\rho<2$. There are $a>0$ and $B\ge0$ with the following property. For every nonzero $z\in\mathbb C$ with $\mathrm{Re}\,z\le a|\mathrm{Im}\,z|$ there are $t>0$ and $D\ge0$ such that $|1-e^{-zt}|\ge\rho$, $e^{\mathrm{Re}\,z\,(s-t)}\le D$ for all $s\in[0,t]$, and
--   $$
--   \frac{Dt}{|1-e^{-zt}|}\le\frac B{|z|}.
--   $$
--
--   This scalar lemma supplies the time parameter in the resolvent estimate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/TimedShiftScalars.lean#L144-L169

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
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent

open OAI OAI.Cotype

theorem OAI.Cotype.exists_sector_timed_shift {ρ : ℝ} (hρ1 : 1 < ρ) (hρ2 : ρ < 2) :
    ∃ a B : ℝ, 0 < a ∧ 0 ≤ B ∧
      ∀ z : ℂ, z ≠ 0 → z.re ≤ a*|z.im| →
        ∃ t D : ℝ, 0 < t ∧ 0 ≤ D ∧
          ρ ≤ ‖1-Complex.exp (-(z*(t : ℂ)))‖ ∧
          (∀ s ∈ Set.Icc 0 t, Real.exp (z.re*(s-t)) ≤ D) ∧
          D*t / ‖1-Complex.exp (-(z*(t : ℂ)))‖ ≤ B/‖z‖ := by sorry
