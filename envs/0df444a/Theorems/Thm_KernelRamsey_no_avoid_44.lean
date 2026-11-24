-- Prove2me | Theorems.Thm_KernelRamsey_no_avoid_44
-- name    : KernelRamsey.no_avoid_44
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:44:38.206803+00:00
-- url     : https://prove2.me/theorems/70c6730a-52fd-4f08-8b55-3c49b09d3868
-- title:
--   No graph on 18 vertices avoids 4-cliques in itself and its complement
-- statement:
--   For every graph $G$ on $18$ vertices, $G$ has a $4$-clique or its complement has a $4$-clique. Together with the Paley graph on $17$ vertices this gives $R(4,4)=18$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem KernelRamsey.no_avoid_44 : ∀ G : SimpleGraph (Fin 18), ¬ (G.CliqueFree 4 ∧ Gᶜ.CliqueFree 4) := by sorry
