-- Prove2me | Theorems.Thm_MatousekLP_Codes_delsarte_psd
-- name    : MatousekLP.Codes.delsarte_psd
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T13:13:33.458777+00:00
-- url     : https://prove2.me/theorems/e19d39be-2274-4c02-acbf-5591efb62abe
-- title:
--   Lemma 8.4.7 — Delsarte's matrix $\tilde M = \sum_i \tilde y_i M_i$ is positive semidefinite
-- statement:
--   Let $C \subseteq \{0,1\}^n$ be a code, let $M_0,\dots,M_n$ be the $2^n\times 2^n$ matrices with $(M_i)_{\mathbf v,\mathbf w} = 1$ if $d_H(\mathbf v,\mathbf w) = i$ and $0$ otherwise, and let
--   $$
--   \tilde y_i = \frac{|\{(\mathbf w,\mathbf w') \in C^2 : d_H(\mathbf w,\mathbf w') = i\}|}{2^n\binom ni}, \qquad i = 0,\dots,n.
--   $$
--   Then the matrix
--   $$
--   \tilde M = \sum_{i=0}^n \tilde y_i M_i
--   $$
--   is positive semidefinite.
--
--   This is Delsarte's original insight; diagonalizing $\tilde M$ in the Hadamard basis turns it into the Krawtchouk inequalities of the linear program, and replacing it by a semidefinite condition is the starting point of Schrijver's stronger bounds.
--
--   **Formalization Note** Positive semidefiniteness is Mathlib's `Matrix.PosSemidef` for real matrices: symmetric, with $\mathbf z^T \tilde M \mathbf z \ge 0$ for every real vector $\mathbf z$ indexed by the words.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 165, Lemma 8.4.7

import Mathlib
import Definitions.Def_MatousekLP_Codes_Basic
import Definitions.Def_MatousekLP_Codes_BoseMesner

open Finset

namespace MatousekLP.Codes

/-- Lemma 8.4.7, p. 165: for every code `C ⊆ {0,1}^n`, the `2^n × 2^n` matrix
`M̃ = ∑_{i=0}^n ỹ_i M_i` is positive semidefinite. -/
theorem delsarte_psd {n : ℕ} (C : Finset (Word n)) : (Mtilde C).PosSemidef := by sorry

end MatousekLP.Codes
