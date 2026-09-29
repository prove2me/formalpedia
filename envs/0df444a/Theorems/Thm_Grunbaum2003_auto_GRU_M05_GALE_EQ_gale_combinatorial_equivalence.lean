-- Prove2me | Theorems.Thm_Grunbaum2003_auto_GRU_M05_GALE_EQ_gale_combinatorial_equivalence
-- name    : Grunbaum2003.auto_GRU_M05_GALE_EQ_gale_combinatorial_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T19:04:16.789984+00:00
-- url     : https://prove2.me/theorems/11a61eb2-459f-4a86-9703-60fd3ed650ac
-- title:
--   Theorem 5.4.5 — Gale data and combinatorial type
-- statement:
--   For two full-dimensional real d-polytopes with injective enumerations V and W of all vertices and Gale transforms G and H, a fixed permutation θ of the vertex indices extends to an isomorphism of the full face posets if and only if, for every index subset J, the origin lies in the relative interior of conv(G(J)) exactly when it lies in the relative interior of conv(H(θ(J))).
-- source:
--   Grünbaum, Convex Polytopes (2003), §5.4, Theorem 5 (5.4.5), printed p.89 / PDF115.

import Definitions.Def_auto_GRU_M05_GALE_EQ_IsDPolytope
import Definitions.Def_auto_GRU_M05_GALE_EQ_PolytopeFace
import Definitions.Def_auto_GRU_M05_GALE_EQ_IsGaleTransform

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem auto_GRU_M05_GALE_EQ_gale_combinatorial_equivalence (d n : ℕ)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (V W : Fin n → (Fin d → ℝ))
    (hVinj : Function.Injective V) (hWinj : Function.Injective W)
    (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (hW : Set.range W = {x | IsExposed ℝ Q {x}})
    (G H : Fin n → (Fin (n - d - 1) → ℝ))
    (hG : IsGaleTransform V G) (hH : IsGaleTransform W H)
    (θ : Equiv.Perm (Fin n)) :
    (∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ (i : Fin n) (F : PolytopeFace P),
        F.val = {V i} → (Φ F).val = {W (θ i)}) ↔
    (∀ J : Set (Fin n),
      (0 : Fin (n - d - 1) → ℝ) ∈ intrinsicInterior ℝ (convexHull ℝ (G '' J)) ↔
      (0 : Fin (n - d - 1) → ℝ) ∈
        intrinsicInterior ℝ (convexHull ℝ (H '' (θ '' J)))) := by sorry

end Grunbaum2003
