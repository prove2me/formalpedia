-- Prove2me | Theorems.Thm_OAI_FiniteBlock_exp_spectral
-- name    : OAI.FiniteBlock.exp_spectral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:28:51.114538+00:00
-- url     : https://prove2.me/theorems/a04086a6-0b6a-494e-b5b9-8b3d11819457
-- title:
--   Spectral formula for the exponential of a Hermitian matrix
-- statement:
--   Let $I$ be a finite index set and let $M\in\mathbb{C}^{I\times I}$ be a Hermitian matrix. Let $U$ be the unitary matrix whose columns are the orthonormal eigenvectors of $M$ chosen by the spectral theorem, and let $\lambda_i\in\mathbb{R}$ be the corresponding eigenvalues, so that $M=U\operatorname{diag}(\lambda_i)U^*$. Then the matrix exponential satisfies
--   $$\exp M=U\,\operatorname{diag}\bigl(e^{\lambda_i}\bigr)_{i\in I}\,U^* .$$
--
--   This explicit diagonalization of $e^{M}$ is used to describe finite-dimensional Gibbs-type perturbations $\rho\propto e^{M}$ of a state on a finite block, whose eigenvalues are $e^{\lambda_i}$ in the eigenbasis of $M$.
--
--   **Formalization Note** $U$ is `hM.eigenvectorUnitary` and $\lambda_i$ is `hM.eigenvalues i` from Mathlib's spectral theorem for Hermitian matrices; $\exp$ is `NormedSpace.exp` in the matrix algebra.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean#L143-L159

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation

open OAI OAI.FiniteBlock
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace Matrix
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem OAI.FiniteBlock.exp_spectral (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    exp M = (hM.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun i => (Real.exp (hM.eigenvalues i) : ℂ)) *
      star (hM.eigenvectorUnitary : Matrix I I ℂ) := by sorry
