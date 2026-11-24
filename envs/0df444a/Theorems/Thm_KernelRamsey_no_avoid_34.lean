-- Prove2me | Theorems.Thm_KernelRamsey_no_avoid_34
-- name    : KernelRamsey.no_avoid_34
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:43:55.496632+00:00
-- url     : https://prove2.me/theorems/f33751d3-1101-45ac-8dd2-c6357480fe9f
-- title:
--   No graph on 9 vertices has no triangle and no independent 4-set
-- statement:
--   For every graph $G$ on $9$ vertices, $G$ has a triangle or its complement has a $4$-clique. Together with the Möbius ladder on $8$ vertices this gives $R(3,4)=9$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.no_avoid_34 : ∀ G : SimpleGraph (Fin 9), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 4) := by sorry
