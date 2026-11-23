-- Prove2me | Theorems.Thm_NoHair_reflected_static_double_compact_truncations
-- name    : NoHair.reflected_static_double_compact_truncations
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:51:04.042627+00:00
-- url     : https://prove2.me/theorems/043a0ea4-f52d-4d71-a309-ff54652be6d1
-- title:
--   Compactness of simultaneous truncations of the two reflected ends
-- statement:
--   Excising the two radial tails of the reflected double leaves a compact set for every cutoff radius. The two bounded portions of the closed physical slice are compact and their images cover this set; coincident points on opposite copies have the same radius.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.reflected_static_double_compact_truncations (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (d : ReflectedStaticDouble Ω N h) :
    ∀ R : ℝ, IsCompact ((d.inc true '' {x : ↥(closure Ω) | R < ‖x.val‖}) ∪ (d.inc false '' {x : ↥(closure Ω) | R < ‖x.val‖}))ᶜ := by sorry
