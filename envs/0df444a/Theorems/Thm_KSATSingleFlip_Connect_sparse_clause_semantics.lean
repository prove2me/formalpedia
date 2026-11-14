-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_sparse_clause_semantics
-- name    : KSATSingleFlip.Connect.sparse_clause_semantics
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:24:27.263721+00:00
-- url     : https://prove2.me/theorems/a2eb7fec-ed18-4d46-b742-8af9c75e4d09
-- title:
--   Sparse k-SAT clauses preserve the formula semantics
-- statement:
--   A sparse width-$k$ clause has exactly $k$ variables and is satisfied exactly when one of its stored literals is true. Every proper $k$-clause has a sparse encoding, and every indexed formula has an encoding preserving clause order and multiplicity. This statement concerns semantic equivalence, not uniform sampling or runtime.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, model printed p. 2 and compact path representation printed p. 32 (PDF p. 34), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SparseFlip

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Sparse k-clauses have exactly the original proper-clause semantics. -/
theorem sparse_clause_semantics (n k m : ℕ) :
    (∀ C : SparseClause n k, (vbl C.toClause).card = k) ∧
    (∀ (C : SparseClause n k) (x : Fin n → Bool), ClauseSat x C.toClause ↔ C.Sat x) ∧
    (∀ D : ProperClause n k, ∃ C : SparseClause n k, C.toClause = D.val) ∧
    (∀ F : Formula n k m, ∃ G : SparseFormula n k m, sparseFormulaSemantics G = ofFormula F) := by
  sorry

end KSATSingleFlip.Connect
