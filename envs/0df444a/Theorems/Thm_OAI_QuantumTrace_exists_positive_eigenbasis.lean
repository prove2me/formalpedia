-- Prove2me | Theorems.Thm_OAI_QuantumTrace_exists_positive_eigenbasis
-- name    : OAI.QuantumTrace.exists_positive_eigenbasis
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:56:35.579342+00:00
-- url     : https://prove2.me/theorems/0188d43b-7f31-4edf-86cc-a7df14ceafba
-- title:
--   A positive operator with finite trace has an eigenbasis with nonnegative eigenvalues summing to the trace
-- statement:
--   Let $E$ be a complex Hilbert space with a Hilbert basis $(b_i)_{i\in\iota}$, and let $T:E\to E$ be a positive bounded operator whose diagonal series converges with sum $\tau$:
--   $$\sum_{i\in\iota}\operatorname{Re}\langle b_i,Tb_i\rangle=\tau .$$
--   Then there exist an index set $J$, a Hilbert basis $(c_j)_{j\in J}$ of $E$ and real numbers $(p_j)_{j\in J}$ such that
--   $$p_j\ge 0\ \text{ for all } j,\qquad \sum_{j\in J}p_j=\tau\ \text{(a convergent series)},\qquad T\,c_j=p_j\,c_j\ \text{ for all } j .$$
--
--   For a density operator ($\tau=1$) this is its spectral decomposition: the eigenvalues form a probability distribution on $J$. This is the basic step that turns statements about quantum states into statements about probability distributions, for example in entropy estimates.
--
--   **Formalization Note** $J$ lives in the same universe as $E$. The hypothesis uses the real parts of the diagonal entries, which for positive $T$ are the entries themselves.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L385-L410

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

theorem OAI.QuantumTrace.exists_positive_eigenbasis (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) :
    ∃ (J : Type u) (c : HilbertBasis J ℂ E) (p : J → ℝ),
      (∀ j, 0 ≤ p j) ∧ HasSum p τ ∧ ∀ j, T (c j) = (p j : ℂ) • c j := by sorry
