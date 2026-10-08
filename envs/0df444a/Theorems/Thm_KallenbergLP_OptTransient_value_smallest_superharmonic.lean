-- Prove2me | Theorems.Thm_KallenbergLP_OptTransient_value_smallest_superharmonic
-- name    : KallenbergLP.OptTransient.value_smallest_superharmonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:53:40.309705+00:00
-- url     : https://prove2.me/theorems/c01447db-9f59-4805-ad82-b0590ace43c1
-- title:
--   Theorem 3.3.2 — the smallest TMD-superharmonic vector
-- statement:
--   Assume a transient policy exists and the transient value vector $w$ is finite. A vector $u\in\mathbb R^E$ is TMD-superharmonic if $u_i\ge r_{ia}+\sum_jp_{iaj}u_j$ for every available state-action pair. The theorem says that $w$ is TMD-superharmonic and lies below every other such vector:
--
--   $$
--   w_i\le u_i\qquad(i\in E)
--   $$
--
--   for every TMD-superharmonic $u$. This identifies the transient value as the minimal solution of the superharmonic inequalities.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 52, Theorem 3.3.2; https://ir.cwi.nl/pub/13008

import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_LinearProgram

namespace KallenbergLP.OptTransient

/-- Theorem 3.3.2, printed p. 52: w is the smallest TMD-superharmonic vector. -/
theorem value_smallest_superharmonic {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α)
    (hex : ∃ R : Policy n α, IsPolicy m R ∧ IsTransient m R)
    (hfin : ∀ i, BddAbove (transientValues m i)) :
    IsSuperharmonic m (optimalValue m) ∧
    ∀ u : Fin n → ℝ, IsSuperharmonic m u → ∀ i, optimalValue m i ≤ u i := by sorry

end KallenbergLP.OptTransient
