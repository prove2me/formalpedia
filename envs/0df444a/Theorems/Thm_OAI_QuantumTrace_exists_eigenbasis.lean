-- Prove2me | Theorems.Thm_OAI_QuantumTrace_exists_eigenbasis
-- name    : OAI.QuantumTrace.exists_eigenbasis
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:54:08.144197+00:00
-- url     : https://prove2.me/theorems/663e953a-ed4c-4359-ae7d-4cdce2760237
-- title:
--   Compact self-adjoint operators admit an orthonormal eigenbasis
-- statement:
--   Let $E$ be a complex Hilbert space and let $T:E\to E$ be a bounded linear operator that is compact and symmetric, i.e. $\langle Tx,y\rangle=\langle x,Ty\rangle$ for all $x,y\in E$. Then there exist an index set $J$, a Hilbert basis $(b_j)_{j\in J}$ of $E$ and complex numbers $(e_j)_{j\in J}$ such that
--   $$T\,b_j=e_j\,b_j\qquad\text{for every } j\in J.$$
--
--   This is the spectral theorem for compact self-adjoint operators in its basis form: $E$ has an orthonormal basis consisting of eigenvectors of $T$. It is the starting point for diagonalizing density operators and other trace-class positive operators, and for defining spectral quantities through such a basis.
--
--   **Formalization Note** The index type $J$ is produced in the same universe as $E$. The eigenvalues are stated as complex numbers; their reality is not part of this statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L257-L288

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

theorem OAI.QuantumTrace.exists_eigenbasis {T : E →L[ℂ] E} (hc : IsCompactOperator T)
    (hs : T.IsSymmetric) :
    ∃ (J : Type u) (b : HilbertBasis J ℂ E) (e : J → ℂ),
      ∀ j, T (b j) = e j • b j := by sorry
