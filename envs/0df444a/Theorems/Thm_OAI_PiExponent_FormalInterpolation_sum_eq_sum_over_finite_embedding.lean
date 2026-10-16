-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_sum_eq_sum_over_finite_embedding
-- name    : OAI.PiExponent.FormalInterpolation.sum_eq_sum_over_finite_embedding
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:00:11.969534+00:00
-- url     : https://prove2.me/theorems/9c10addf-5901-4150-836d-549da42c706f
-- title:
--   Reindex a finitely supported sum along an injective finite embedding
-- statement:
--   For an injective map from a finite type into an arbitrary type, reindex a sum over a finite set covered by the map as a sum over the whole finite domain, provided the coefficient function vanishes outside that set.

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.sum_eq_sum_over_finite_embedding
    {α β R : Type*} [DecidableEq α] [Fintype β] [CommSemiring R]
    (S : Finset α) (f : β → α) (a g : α → R)
    (hf : Function.Injective f)
    (hcover : ∀ x ∈ S, ∃ b, f b = x)
    (hzero : ∀ x, x ∉ S → a x = 0) :
      ∑ x ∈ S, a x * g x = ∑ b : β, g (f b) * a (f b) := by sorry
