-- Prove2me | Theorems.Thm_FullFormalization_exists_unit_hidden_direction
-- name    : FullFormalization.exists_unit_hidden_direction
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T06:22:57.886003+00:00
-- url     : https://prove2.me/theorems/df3ddac0-64d7-498e-80fc-f1663fd1ffa9
-- title:
--   Unit hidden direction $u = v/\|v\|$ of (24.3)–(24.5)
-- statement:
--   For every $N$ and every query family $q_1,\dots,q_N \in \mathbb{R}^{2N+1}$ there exists a unit vector $u$ whose first $N$ coordinates vanish and which is orthogonal to all query points:
--   $$ \|u\| = 1, \qquad u_1 = \cdots = u_N = 0, \qquad \langle u, q_i\rangle = 0 \quad (i = 1,\dots,N). $$
--   It is obtained by normalising the nonzero vector $v$ of Lemma 24.1, $u = v/\|v\|$ (24.3), written in Lean as $u = \|v\|^{-1}\cdot v$; the norm is the Euclidean norm and the bracket the Euclidean inner product. Both the vanishing-coordinate condition (24.4) and the orthogonality conditions (24.5) are inherited from $v$ because they are homogeneous in the vector.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §24, eq. (24.3)–(24.5); Lean: FullFormalization.HiddenDirection lines 187–202

-- Generated from F:/20261008/FullFormalization\FullFormalization\HiddenDirection.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.HiddenDirection

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 24
  (lines ~2175-2251), Lemma 24.1 and equations (24.1)-(24.5).

  The source document fixes the dimension

      D = 2 N + 1                                              (23.1)

  and, after fixing the seed, obtains `N` query points `q_1, ..., q_N ∈ ℝ^D`
  which are completely determined by `N`, `D` and the public sampling rule;
  in particular the query positions do not depend on function values.  It then
  asks for a *nonzero* vector `v` with

      v_1 = ... = v_N = 0,                                     (24.1)
      ⟨v, q_i⟩ = 0        for i = 1, ..., N,                   (24.2)

  and proves (Lemma 24.1) that such a `v` necessarily exists.

  Formalisation notes.

  * `Fin N` is the Lean index type for `i = 1, ..., N`; the source index `i`
    corresponds to `Fin` value `i - 1`.  Accordingly (24.1) -- `v_1 = ... = v_N = 0`
    -- says that the first `N` coordinates `v 0, ..., v (N-1)` vanish, which is
    encoded as `∀ i : Fin N, v (Fin.castLE _ i) = 0`; the map
    `Fin.castLE (by omega : N ≤ 2 * N + 1)` is the inclusion of the first `N`
    coordinates into `Fin (2 * N + 1)`.

  * The ambient space is `EuclideanSpace ℝ (Fin (2 * N + 1))`, i.e. `Fin D → ℝ`
    with the Pi inner product, exactly as in the source.

  * Lemma 24.1 is *proved*, not assumed: `exists_nonzero_orthogonal_of_finrank_succ`
    below isolates the pure dimension argument of the source ("the last `N + 1`
    coordinates span a subspace of dimension `N + 1`; the `N` homogeneous
    orthogonality conditions impose at most `N` independent linear constraints;
    hence the common kernel has dimension at least `(N + 1) - N = 1`"), and
    `finrank_vanishingFirstBlock` computes the dimension of the constrained
    subspace.  No axiom, `sorry` or `unsafe` is used anywhere in this file.

  * (24.3) writes `u = v / ‖v‖`.  This Mathlib revision has no scalar-division
    instance on `EuclideanSpace`, so the division is written as multiplication
    by `‖v‖⁻¹` (`normalizeVec`); `normalizeVec_eq` records the equality with the
    source's `v / ‖v‖`.
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_HiddenDirection
import Theorems.Thm_FullFormalization_exists_hidden_direction
import Theorems.Thm_FullFormalization_exists_nonzero_orthogonal_of_finrank_succ
import Theorems.Thm_FullFormalization_finrank_vanishingFirstBlock
import Theorems.Thm_FullFormalization_firstBlockProj_surjective
import Theorems.Thm_FullFormalization_norm_normalizeVec

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

noncomputable section

variable {N : ℕ}

/-! ## Lemma 24.1, abstract dimension argument

The source's proof only uses: a subspace of dimension `N + 1` in a real inner
product space, and `N` homogeneous linear constraints `⟨·, q i⟩ = 0`.  We prove
that abstract statement first, so that the dimension count is auditable on its
own, independently of the concrete coordinates in `Fin (2 * N + 1)`. -/



/-! ## The concrete subspace of (24.1)

`firstBlockProj N` is the linear map `v ↦ (v 0, ..., v (N-1))` that reads off the
first `N` coordinates of a vector of `EuclideanSpace ℝ (Fin (2 * N + 1))`; its
kernel is the subspace cut out by the conditions (24.1). -/









/-! ## Lemma 24.1 for the source's query points -/



/-! ## The unit vector `u = v / ‖v‖` of (24.3)-(24.5) -/









end

end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
variable {N : ℕ}

theorem FullFormalization.exists_unit_hidden_direction (N : ℕ) (q : Fin N → EuclideanSpace ℝ (Fin (2 * N + 1))) :
    ∃ u : EuclideanSpace ℝ (Fin (2 * N + 1)),
      ‖u‖ = 1 ∧ (∀ i : Fin N, u (Fin.castLE (by omega) i) = 0) ∧
        (∀ i : Fin N, ⟪u, q i⟫ = 0) := by sorry
