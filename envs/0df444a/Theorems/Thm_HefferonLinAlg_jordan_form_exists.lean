-- Prove2me | Theorems.Thm_HefferonLinAlg_jordan_form_exists
-- name    : HefferonLinAlg.jordan_form_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T04:01:49.393367+00:00
-- url     : https://prove2.me/theorems/928bfc29-9a7a-415c-9ee3-6f059bd1faf2
-- title:
--   Every square complex matrix is similar to a Jordan form matrix
-- statement:
--   Let $A$ be an $n \times n$ matrix over $\mathbb{C}$. Then $A$ has a Jordan form: there are a block count $k$, nonempty block sizes $sz : \mathrm{Fin}\,k \to \mathbb{N}$, eigenvalues $\lambda : \mathrm{Fin}\,k \to \mathbb{C}$, a reindexing $e$ of the coordinates by the block index type, and an invertible matrix $P$, such that $P^{-1} A P$ is the block-diagonal Jordan matrix built from those blocks, transported along $e$. Equivalently: **every square complex matrix is similar to a matrix in Jordan form.** This is Hefferon's Theorem 2.8 exactly as he states it — the existence half of the canonical form. Mathlib has the generalized eigenspace decomposition but no Jordan canonical form, so this is a genuine formalization target.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Five, Section IV.2, Theorem 2.8, printed p. 454 (PDF p. 464)

import Mathlib
import Definitions.Def_HefferonLinAlg_jordan

open Matrix

namespace HefferonLinAlg

theorem jordan_form_exists
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : HasJordanForm A := by
  sorry

end HefferonLinAlg
