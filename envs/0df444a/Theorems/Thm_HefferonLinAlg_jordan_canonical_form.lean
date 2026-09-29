-- Prove2me | Theorems.Thm_HefferonLinAlg_jordan_canonical_form
-- name    : HefferonLinAlg.jordan_canonical_form
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T04:02:04.022183+00:00
-- url     : https://prove2.me/theorems/be7512f2-f839-45cc-82bf-d8306cce090c
-- title:
--   Jordan canonical form: existence and uniqueness of the block multiset
-- statement:
--   Let $A$ be an $n \times n$ matrix over $\mathbb{C}$. There is **exactly one** multiset $B$ of $(\text{block size}, \text{eigenvalue})$ pairs arising as the Jordan block data of $A$: some Jordan form of $A$ has block multiset $B$, and every Jordan form of $A$ has that same multiset.
--
--   Existence is Hefferon's Theorem 2.8 — every square complex matrix is similar to a Jordan matrix. Uniqueness is his Remark 2.9, which observes that to be a genuine canonical form for matrix similarity the Jordan form must be unique, and which the book states but does not prove. Together they are what the phrase *canonical form* means.
--
--   Passing to a multiset is what expresses 'unique up to reordering the blocks': the blocks may be listed in any order, but which blocks occur, and with what multiplicity, is determined by $A$. Requiring every block to be nonempty is what makes this true — empty blocks could otherwise be padded on carrying arbitrary eigenvalues. Mathlib has the generalized eigenspace decomposition but no Jordan canonical form, so this is a genuine formalization target.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Five, Section IV.2, Theorem 2.8 (printed p. 454) and Remark 2.9 (printed p. 456)

import Mathlib
import Definitions.Def_HefferonLinAlg_jordan

open Matrix

namespace HefferonLinAlg

theorem jordan_canonical_form
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃! B : Multiset (ℕ × ℂ),
      ∃ (k : ℕ) (sz : Fin k → ℕ) (lam : Fin k → ℂ),
        IsJordanFormOf A sz lam ∧ jordanBlocks sz lam = B := by
  sorry

end HefferonLinAlg
