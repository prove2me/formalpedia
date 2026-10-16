-- Prove2me | Theorems.Thm_OAI_QuantumTrace_basisApprox_norm_sub_le
-- name    : OAI.QuantumTrace.basisApprox_norm_sub_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:53:34.850974+00:00
-- url     : https://prove2.me/theorems/e595d0b8-6f06-4e2c-b0ec-c74bbf9967e2
-- title:
--   Operator-norm error of the finite basis truncation of a Hilbert–Schmidt operator
-- statement:
--   Let $E$ and $F$ be complex inner product spaces, let $(b_i)_{i\in\iota}$ be a Hilbert basis of $E$, and let $T:E\to F$ be a bounded linear operator such that the series $\sum_{i\in\iota}\|Tb_i\|^2$ converges with sum $\tau$. For a finite set $s\subseteq\iota$, let $T_s$ be the finite-rank truncation
--   $$T_s x=\sum_{i\in s}\langle b_i,x\rangle\,Tb_i \qquad(x\in E),$$
--   which agrees with $T$ on $b_i$ for $i\in s$ and vanishes on $b_i$ for $i\notin s$. Then
--   $$\|T-T_s\|\le\sqrt{\tau-\sum_{i\in s}\|Tb_i\|^2}.$$
--
--   Since the right-hand side is the square root of the tail of a convergent series, it tends to $0$ along finite sets increasing to $\iota$. The estimate therefore exhibits an operator with square-summable basis images as an operator-norm limit of finite-rank operators, which is the standard route to compactness of Hilbert–Schmidt operators.
--
--   **Formalization Note** $T_s$ is `basisApprox b T s`, the finite sum of rank-one maps `rankOne ℂ (T (b i)) (b i)`. Completeness of $E$ and $F$ is not assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L205-L219

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open Filter ContinuousLinearMap InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

omit [CompleteSpace E] [CompleteSpace F] in
theorem OAI.QuantumTrace.basisApprox_norm_sub_le (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    {τ : ℝ} (ht : HasSum (fun i => ‖T (b i)‖ ^ 2) τ) (s : Finset ι) :
    ‖T - basisApprox b T s‖ ≤ Real.sqrt (τ - ∑ i ∈ s, ‖T (b i)‖ ^ 2) := by sorry
