-- Prove2me | Theorems.Thm_KernelRamsey_no_avoid_33
-- name    : KernelRamsey.no_avoid_33
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:42.711025+00:00
-- url     : https://prove2.me/theorems/ad7cd144-b700-4a15-bd3c-368ae066ac38
-- title:
--   No graph on 6 vertices avoids triangles in itself and its complement
-- statement:
--   For every graph $G$ on $6$ vertices, $G$ has a triangle or its complement has a triangle. Together with the 5-cycle this gives $R(3,3)=6$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.no_avoid_33 : ∀ G : SimpleGraph (Fin 6), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3) := by sorry
