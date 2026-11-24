-- Prove2me | Theorems.Thm_HodgeComputer_Formal_HoldoutCover_piola_divergence
-- name    : HodgeComputer.Formal.HoldoutCover.piola_divergence
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:20:39.479396+00:00
-- url     : https://prove2.me/theorems/242e33fe-65c3-4b96-8660-19519ea6d057
-- title:
--   Piola identity for field divergence under a coordinate change
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type with decidable equality, and $D, E : \iota \to \operatorname{Der}_{\mathbb{Z}}(K, K)$ two families of derivations linked by an invertible matrix $M, N \in \operatorname{Mat}_{\iota \times \iota}(K)$ with $\det M \neq 0$, $N M = I$, the chain rule
--
--   $$E_j(z) = \sum_{k \in \iota} N_{kj} D_k(z),$$
--
--   and the mixed-partial symmetry $D_k(M_{ji}) = D_i(M_{jk})$ for all $i, j, k$. Then for every vector $u : \iota \to K$, the Piola pushforward $v_j = \sum_i (u_i / \det M) M_{ji}$ satisfies
--
--   $$\sum_{j \in \iota} E_j(v_j) = \frac{1}{\det M} \sum_{i \in \iota} D_i(u_i).$$
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/HoldoutCover/Piola.lean#L1-L162

import Definitions.Def_HodgeComputerFormal_Algebra
import Mathlib.LinearAlgebra.Matrix.Adjugate
set_option autoImplicit false
open scoped BigOperators

theorem HodgeComputer.Formal.HoldoutCover.piola_divergence
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (D E : ι → Derivation ℤ K K)
    (M N : Matrix ι ι K) (hdet : M.det ≠ 0) (hNM : N * M = 1)
    (chain : ∀ j z, E j z = ∑ k, N k j * D k z)
    (mixed : ∀ i j k, D k (M j i) = D i (M j k))
    (u : ι → K) :
    HoldoutConstruction.fieldDivergence E (fun j => ∑ i, (u i / M.det) * M j i) =
      HoldoutConstruction.fieldDivergence D u / M.det := by sorry
