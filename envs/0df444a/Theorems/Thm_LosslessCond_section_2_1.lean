-- Prove2me | Theorems.Thm_LosslessCond_section_2_1
-- name    : LosslessCond.section_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:33:48.529276+00:00
-- url     : https://prove2.me/theorems/77a096f7-3222-4fce-b8c9-a5476a176acc
-- title:
--   §2.1 — deleting duplicate row or column values preserves $D$ and rank
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite Boolean matrix, and write $D(M[U,V])$ for the communication complexity of the submatrix on $U\times V$ and $\operatorname{rank}$ for the rank over $\mathbb R$.
--
--   1. **Columns.** If $V_0\subseteq V$ and every column $y\in V$ agrees on $U$ with some $y_0\in V_0$ (that is, $M(x,y)=M(x,y_0)$ for all $x\in U$), then $D(M[U,V_0])=D(M[U,V])$.
--   2. **Rows.** If $U_0\subseteq U$ and every row $x\in U$ agrees on $V$ with some $x_0\in U_0$, then $D(M[U_0,V])=D(M[U,V])$.
--   3. **Rank, columns.** If every column of $M$ equals some column with label in $V_0$, then $\operatorname{rank} M[X,V_0]=\operatorname{rank} M$.
--   4. **Rank, rows.** If every row of $M$ equals some row with label in $U_0$, then $\operatorname{rank} M[U_0,Y]=\operatorname{rank} M$.
--
--   Keeping one representative of each value therefore loses neither communication complexity nor rank; Lemma 5.2 uses this to work with at most $2^r$ column representatives.
--
--   Differences from the source:
--   - generalization: one original representative of each value → any subset containing at least one representative of each value; reason: a set of exactly one representative per value satisfies the hypothesis
--   - generalization: the whole matrix M (communication clauses) → any submatrix M[U, V]; reason: the paper's statement is the case U = X, V = Y; M[U, V] is itself a finite Boolean matrix
--   - encoding: D(M[U, V]) for the submatrix on U × V → DetCCHard.commCost M U V, the least depth of a protocol on all of X, Y correct on U × V; reason: protocols restrict and extend, so the two costs agree on every instance
--   - encoding: finite nonempty input sets X, Y → finite types X Y : Type (Fintype), nonemptiness not assumed; reason: every finite set is equivalent to a type in universe 0; where nonemptiness matters it is assumed or forced by the other hypotheses
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), §2.1 Repeated input values, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_realRank

namespace LosslessCond

/-- **Repeated input values** (Mackenzie, *Lossless Hardness Condensation in Deterministic
Communication Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, §2.1, p.7): deleting
duplicate column values preserves communication complexity and rank, and the same holds for rows.

1. Columns: if `V₀ ⊆ V` and every column `y ∈ V` has the same values on `U` as some `y₀ ∈ V₀`,
   then `D(M[U, V₀]) = D(M[U, V])`.
2. Rows: if `U₀ ⊆ U` and every row `x ∈ U` has the same values on `V` as some `x₀ ∈ U₀`, then
   `D(M[U₀, V]) = D(M[U, V])`.
3. Rank, columns: if every column of `M` equals some column in `V₀`, the submatrix on the columns
   `V₀` has the same real rank as `M`.
4. Rank, rows: if every row of `M` equals some row in `U₀`, the submatrix on the rows `U₀` has the
   same real rank as `M`.

**Formalization Note** The paper keeps exactly one representative of each value; here `V₀`
(resp. `U₀`) is any subset containing at least one representative of each value, which includes
that case. The communication clauses are stated for an arbitrary submatrix `M[U, V]`, encoded as
`DetCCHard.commCost M U V`; the paper's whole-matrix statement is `U = X`, `V = Y`. -/
theorem section_2_1 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) :
    (∀ (U : Set X) (V V₀ : Set Y), V₀ ⊆ V → (∀ y ∈ V, ∃ y₀ ∈ V₀, ∀ x ∈ U, M x y = M x y₀) →
      DetCCHard.commCost M U V₀ = DetCCHard.commCost M U V) ∧
    (∀ (U U₀ : Set X) (V : Set Y), U₀ ⊆ U → (∀ x ∈ U, ∃ x₀ ∈ U₀, ∀ y ∈ V, M x y = M x₀ y) →
      DetCCHard.commCost M U₀ V = DetCCHard.commCost M U V) ∧
    (∀ V₀ : Finset Y, (∀ y, ∃ y₀ ∈ V₀, ∀ x, M x y = M x y₀) →
      DetCCHard.realRank (fun x (y : V₀) => M x y) = DetCCHard.realRank M) ∧
    (∀ U₀ : Finset X, (∀ x, ∃ x₀ ∈ U₀, ∀ y, M x y = M x₀ y) →
      DetCCHard.realRank (fun (x : U₀) y => M x y) = DetCCHard.realRank M) := by sorry

end LosslessCond
