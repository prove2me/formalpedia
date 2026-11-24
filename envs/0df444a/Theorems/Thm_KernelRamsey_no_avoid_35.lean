-- Prove2me | Theorems.Thm_KernelRamsey_no_avoid_35
-- name    : KernelRamsey.no_avoid_35
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:44:08.283594+00:00
-- url     : https://prove2.me/theorems/b3f1a5b8-546f-43f7-bd96-548e898f6c92
-- title:
--   No graph on 14 vertices has no triangle and no independent 5-set
-- statement:
--   For every graph $G$ on $14$ vertices, $G$ has a triangle or its complement has a $5$-clique. Together with the circulant graph on $13$ vertices this gives $R(3,5)=14$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.no_avoid_35 : ∀ G : SimpleGraph (Fin 14), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 5) := by sorry
