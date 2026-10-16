-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_block_crossEntropy
-- name    : OAI.EntropyPhotonNumber.block_crossEntropy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:35:37.020312+00:00
-- url     : https://prove2.me/theorems/a9a0f53e-ba51-4433-a670-6127a8952315
-- title:
--   Cross-entropy against a block-modified spectral state
-- statement:
--   Let $F=\ell^2(\mathbb{N}^n,\mathbb{C})$ be the $n$-mode Fock space. Let $I$ be a finite set and $J$ any set, let $(b_k)_{k\in I\sqcup J}$ be a Hilbert basis of $F$, and let $p:I\sqcup J\to(0,\infty)$ with $\sum_kp_k=1$. For a matrix $A\in\mathbb{C}^{I\times I}$ let
--   $$\mathsf B(A)=\sum_{i,i'\in I}A_{ii'}\,|b_i\rangle\langle b_{i'}|$$
--   be its embedding as an operator acting on the span of the finite block $\{b_i:i\in I\}$. Let $M\in\mathbb{C}^{I\times I}$ be Hermitian with orthonormal eigenvectors $c_i\in\mathbb{C}^I$ and eigenvalues $\lambda_i$ (as chosen by the spectral theorem). The *block-modified basis* is $a_i=\sum_{i'}(c_i)_{i'}\,b_{i'}$ for $i\in I$ and $a_j=b_j$ for $j\in J$; the partition function is $\mathcal Z=\sum_{j\in J}p_j+\sum_{i\in I}e^{\lambda_i}>0$, and the modified weights are $w_i=e^{\lambda_i}/\mathcal Z$ $(i\in I)$, $w_j=p_j/\mathcal Z$ $(j\in J)$, which are positive and sum to $1$. The *block state* is the state $\rho_M=\sum_{k\in I\sqcup J}w_k\,|a_k\rangle\langle a_k|$.
--
--   For a state $\sigma$ write $\mathbb E_\sigma(T)=\operatorname{Tr}(\sigma T)$ (computed as $\sum_k\langle\sqrt\sigma|k\rangle,T\sqrt\sigma|k\rangle\rangle$ over the number basis) and define the cross-entropy of $\sigma$ relative to the spectral data $(b,p)$ as
--   $$H(\sigma\,\|\,b,p)=\sum_{k\in I\sqcup J}\bigl(-\log p_k\bigr)\,\langle b_k,\sigma b_k\rangle .$$
--
--   **Theorem.** Let $\sigma$ be a state such that the series $\sum_k(-\log p_k)\langle b_k,\sigma b_k\rangle$ converges (absolutely). Then the series $\sum_k(-\log w_k)\,\langle a_k,\sigma a_k\rangle$ converges, and
--   $$\sum_{k\in I\sqcup J}\bigl(-\log w_k\bigr)\,\langle a_k,\sigma a_k\rangle=H(\sigma\,\|\,b,p)+\operatorname{Re}\mathbb E_\sigma\bigl(\mathsf B(\operatorname{diag}(\log p_i)_{i\in I})\bigr)-\operatorname{Re}\mathbb E_\sigma\bigl(\mathsf B(M)\bigr)+\log\mathcal Z .$$
--
--   The left side is the cross-entropy $-\operatorname{Tr}\sigma\log\rho_M$ of $\sigma$ against the block state $\rho_M$ (eigenbasis $a$, eigenvalues $w$). The formula expresses it through the unperturbed cross-entropy and two finite-block expectations, which makes the dependence on $M$ explicit (affine in $M$ plus $\log\mathcal Z$) for variational arguments.
--
--   **Formalization Note** The values $\langle b_k,\sigma b_k\rangle$ are written as real parts of complex inner products, the identity is a `HasSum` statement, and $H(\sigma\|b,p)$ is the `tsum` `crossEntropy b p σ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean#L694-L743

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
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

theorem OAI.EntropyPhotonNumber.block_crossEntropy (σ : State n) (b : HilbertBasis (I ⊕ J) ℂ (Fock n))
    (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (hc : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re))
    (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    HasSum (fun j => (-Real.log (FiniteBlock.weights p M hM j))*
      (inner ℂ (FiniteBlock.basis b hM.eigenvectorBasis j)
        (σ.op (FiniteBlock.basis b hM.eigenvectorBasis j))).re)
      (crossEntropy b p σ+
        (expectation σ (FiniteBlock.block b (Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ))))).re-
        (expectation σ (FiniteBlock.block b M)).re+Real.log (FiniteBlock.partition p M hM)) := by sorry
