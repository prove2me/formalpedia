-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_blockState_operator
-- name    : OAI.EntropyPhotonNumber.blockState_operator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:34:05.401991+00:00
-- url     : https://prove2.me/theorems/04ce5923-61e9-4791-a075-fa7215da00ec
-- title:
--   Operator formula for a state whose finite spectral block is replaced by $e^{M}$
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space. Let $I$ be a finite set and $J$ any set, let $(b_k)_{k\in I\sqcup J}$ be a Hilbert basis of $F$, and let $p:I\sqcup J\to(0,\infty)$ with $\sum_kp_k=1$. For a matrix $A\in\mathbb{C}^{I\times I}$ let
--   $$\mathsf B(A)=\sum_{i,i'\in I}A_{ii'}\,|b_i\rangle\langle b_{i'}|$$
--   be its embedding as an operator acting on the span of the finite block $\{b_i:i\in I\}$. Let $M\in\mathbb{C}^{I\times I}$ be Hermitian with orthonormal eigenvectors $c_i\in\mathbb{C}^I$ and eigenvalues $\lambda_i$ (as chosen by the spectral theorem). The *block-modified basis* is $a_i=\sum_{i'}(c_i)_{i'}\,b_{i'}$ for $i\in I$ and $a_j=b_j$ for $j\in J$; the partition function is $\mathcal Z=\sum_{j\in J}p_j+\sum_{i\in I}e^{\lambda_i}>0$, and the modified weights are $w_i=e^{\lambda_i}/\mathcal Z$ $(i\in I)$, $w_j=p_j/\mathcal Z$ $(j\in J)$, which are positive and sum to $1$. The *block state* is the state $\rho_M=\sum_{k\in I\sqcup J}w_k\,|a_k\rangle\langle a_k|$.
--
--   **Theorem.** If $\rho$ is a state with $\rho\,b_k=p_k\,b_k$ for all $k\in I\sqcup J$, then
--   $$\rho_M=\mathcal Z^{-1}\Bigl(\rho+\mathsf B(\exp M)-\mathsf B\bigl(\operatorname{diag}(p_i)_{i\in I}\bigr)\Bigr).$$
--
--   So $\rho_M$ is obtained from $\rho$ by replacing its restriction $\operatorname{diag}(p_i)$ to a finite spectral block by the positive matrix $e^{M}$ and renormalizing. Such block states give finite-dimensional variations of a Gibbs-type state along which first- and second-order (Hessian) conditions of a variational problem can be computed.
--
--   **Formalization Note** The block state is `blockState b p hp hs M hM`, defined as `spectralState` of the basis `FiniteBlock.basis b hM.eigenvectorBasis` with weights `FiniteBlock.weights`; $\mathsf B$ is `FiniteBlock.block b` and $\mathcal Z$ is `FiniteBlock.partition`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean#L658-L686

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

open OAI OAI.EntropyPhotonNumber
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
open NormedSpace
open scoped Matrix.Norms.Operator
open QuantumTrace TraceEnsemble
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

theorem OAI.EntropyPhotonNumber.blockState_operator (ρ : State n) (b : HilbertBasis (I ⊕ J) ℂ (Fock n))
    (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    (blockState b p hp hs M hM).op = ((FiniteBlock.partition p M hM : ℂ)⁻¹) •
      (ρ.op+FiniteBlock.block b (exp M)-FiniteBlock.block b (Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ)))) := by sorry
