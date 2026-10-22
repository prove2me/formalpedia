-- Prove2me | Theorems.Thm_FullFormalization_exists_nonzero_orthogonal_of_finrank_succ
-- name    : FullFormalization.exists_nonzero_orthogonal_of_finrank_succ
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:45:51.606986+00:00
-- url     : https://prove2.me/theorems/d071648c-96af-4b41-95e7-ec63925cccf8
-- title:
--   Abstract rank-nullity core of Lemma 24.1
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, let $K \subseteq E$ be a linear subspace with $\dim K = N+1$, and let $q_1,\dots,q_N \in E$ be an arbitrary finite family of query vectors. Then $K$ contains a nonzero vector orthogonal to every $q_i$:
--   $$ \exists\, v \in K:\quad v \neq 0 \quad\text{and}\quad \langle v, q_i\rangle = 0 \ \ (i = 1,\dots,N). $$
--   Equivalently, the linear map $\psi : K \to \mathbb{R}^{N}$, $\psi(x)_i = \langle x, q_i\rangle$, has a kernel of dimension at least $(N+1) - N = 1$. Here the bracket is the inner product of $E$, and the codomain of $\psi$ is the $N$-dimensional space of $N$-tuples, which is what bounds the number of independent linear constraints by $N$.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §24, proof of Lemma 24.1 (lines 2205–2223); Lean: FullFormalization.HiddenDirection lines 66–106

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

theorem FullFormalization.exists_nonzero_orthogonal_of_finrank_succ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Submodule ℝ E) (hK : Module.finrank ℝ ↥K = N + 1) (q : Fin N → E) :
    ∃ v ∈ K, v ≠ 0 ∧ ∀ i, ⟪v, q i⟫ = 0 := by sorry
