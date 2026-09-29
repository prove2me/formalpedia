-- Prove2me | Theorems.Thm_NumberField_InfinitePlace_isOpen_range_powMonoidHom_units_completion
-- name    : NumberField.InfinitePlace.isOpen_range_powMonoidHom_units_completion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/0a21c497-180c-5f7a-97e6-c7463eb00fbe
-- title:
--   Openness of n-th powers in K_w^× at an infinite place
-- statement:
--   Let $K$ be a field, let $w$ be an infinite place of $K$ in the sense of Mathlib's `NumberField.InfinitePlace K`, and let $n$ be a natural number with $0 < n$. Write $K_w$ for the completion `w.Completion` of $K$ at $w$, a topological field, and $K_w^\times$ for its unit group with the induced topology. Consider the monoid endomorphism $u \mapsto u^n$ of $K_w^\times$ given by `powMonoidHom n`. The assertion is that the image of this homomorphism, i.e. the subgroup $(K_w^\times)^n$ of $n$-th powers, is an open subset of $K_w^\times$. Note that $K$ is only assumed to be a field; no number-field hypothesis enters, and the positivity hypothesis $0 < n$ is genuinely needed, since for $n = 0$ the image is the trivial subgroup, which is not open.
--
--   This is the archimedean half of the standard fact that the $n$-th power subgroup of the multiplicative group of a local field is open, the companion statement at finite places being the nonarchimedean one. It is used in the proof that the idelic norm has open image, [`M4aHerbrand.AdeleBaseChange.isOpen_range_idelicNorm`](thm.html#M4aHerbrand.AdeleBaseChange.isOpen_range_idelicNorm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfinitePlace_isOpen_range_powMonoidHom_units_completion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.InfinitePlace.isOpen_range_powMonoidHom_units_completion {K : Type*} [Field K]
    (w : NumberField.InfinitePlace K) {n : ℕ} (hn : 0 < n) :
    IsOpen ((powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range : Set (w.Completion)ˣ) := by sorry
