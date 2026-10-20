-- Prove2me | Theorems.Thm_OAI_Cotype_exists_exact_amplified_pairing
-- name    : OAI.Cotype.exists_exact_amplified_pairing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:28:50.104351+00:00
-- url     : https://prove2.me/theorems/f638abba-14d0-497f-aea3-f688111e4433
-- title:
--   Exact Walsh pairings after l2 amplification
-- statement:
--   Let $X,Y$ be real normed spaces, $T:X\to Y$ nonzero and $n\in\mathbb N$, with Walsh norm $\omega_n(T)$. Let $\Omega=\{0,1\}^{2n}$ and $T^{(2)}=T\otimes\mathrm{id}:\ell_2(\Omega;X)\to\ell_2(\Omega;Y)$ act coordinatewise. There are $\gamma>\max(0,\omega_n(T)/2)$, unit-ball vectors $x_u\in\ell_2(\Omega;X)$ and unit-ball functionals $y_v\in\ell_2(\Omega;Y)^*$, indexed by $u,v\in\{0,1\}^n$, such that
--   $$
--   y_v\bigl(T^{(2)}x_u\bigr)=\gamma\,\chi_v(u)\qquad\text{for all }u,v .
--   $$
--   Moreover $\omega_k(T^{(2)})=\omega_k(T)$ for every $k$.
--
--   After amplification, the Walsh matrix is realized exactly by a bounded biorthogonal-type system.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/WalshExactPairing.lean#L115-L133

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
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing

open OAI OAI.Cotype
open scoped BigOperators
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem OAI.Cotype.exists_exact_amplified_pairing (n : ℕ) {T : X →L[ℝ] Y} (hT : T ≠ 0) :
    ∃ (γ : ℝ)
      (x : Cube n → PiLp 2 (fun _ : Cube (n+n) => X))
      (y : Cube n → (PiLp 2 (fun _ : Cube (n+n) => Y) →L[ℝ] ℝ)),
      walshNorm n T / 2 < γ ∧ 0 < γ ∧
      (∀ u, ‖x u‖ ≤ 1) ∧ (∀ v, ‖y v‖ ≤ 1) ∧
      (∀ u v, y v (l2Amplification T (x u)) = γ * character v u) ∧
      (∀ k, walshNorm k (l2Amplification (Ω := Cube (n+n)) T) = walshNorm k T) := by sorry
