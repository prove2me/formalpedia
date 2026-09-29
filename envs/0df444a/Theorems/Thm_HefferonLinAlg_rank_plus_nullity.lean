-- Prove2me | Theorems.Thm_HefferonLinAlg_rank_plus_nullity
-- name    : HefferonLinAlg.rank_plus_nullity
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-05T05:33:40.438925+00:00
-- url     : https://prove2.me/theorems/34959ed9-e56a-4204-8d4d-c3e5f5ffae06
-- title:
--   Rank plus nullity equals the dimension of the domain
-- statement:
--   Let $f : V \to W$ be a linear map of vector spaces over a field $K$, with $V$ finite-dimensional. Then the dimension of the range space of $f$ plus the dimension of its null space equals the dimension of $V$. Hefferon presents this as the map-level analogue of 'general = particular + homogeneous' for a linear system.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Three, Section II.2, Theorem 2.14, p. 213

import Mathlib

namespace HefferonLinAlg

theorem rank_plus_nullity
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.ker f) =
      Module.finrank K V := by
  sorry

end HefferonLinAlg
