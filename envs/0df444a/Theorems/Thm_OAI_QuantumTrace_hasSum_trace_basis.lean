-- Prove2me | Theorems.Thm_OAI_QuantumTrace_hasSum_trace_basis
-- name    : OAI.QuantumTrace.hasSum_trace_basis
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:55:14.251272+00:00
-- url     : https://prove2.me/theorems/d2ebaa61-059f-4df8-a510-59a627a5216a
-- title:
--   The trace of a positive operator does not depend on the orthonormal basis
-- statement:
--   Let $E$ be a complex Hilbert space, let $(b_i)_{i\in\iota}$ and $(c_j)_{j\in\kappa}$ be two Hilbert bases of $E$, and let $T:E\to E$ be a positive bounded operator. If the diagonal series of $T$ in the basis $(b_i)$ converges with sum $\tau\in\mathbb{R}$,
--   $$\sum_{i\in\iota}\operatorname{Re}\langle b_i,Tb_i\rangle=\tau,$$
--   then the diagonal series in the basis $(c_j)$ also converges, with the same sum:
--   $$\sum_{j\in\kappa}\operatorname{Re}\langle c_j,Tc_j\rangle=\tau .$$
--
--   Thus finiteness of the trace of a positive operator, and its value, do not depend on the basis. In particular, the normalization of a density operator may be checked in any convenient orthonormal basis, for example the number basis or an eigenbasis.
--
--   **Formalization Note** Both sums are unconditional sums (`HasSum`), so the conclusion includes summability. For positive $T$ the diagonal entries are real and nonnegative; the real part is taken because the inner product is complex-valued.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L363-L383

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

theorem OAI.QuantumTrace.hasSum_trace_basis (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) :
    HasSum (fun i => (inner ℂ (c i) (T (c i))).re) τ := by sorry
