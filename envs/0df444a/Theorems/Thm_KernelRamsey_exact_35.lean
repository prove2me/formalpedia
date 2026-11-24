-- Prove2me | Theorems.Thm_KernelRamsey_exact_35
-- name    : KernelRamsey.exact_35
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:27:50.380525+00:00
-- url     : https://prove2.me/theorems/c7252387-e214-49ea-bacc-07df6b12111a
-- title:
--   The exact value $R(3,5)=14$
-- statement:
--   There is a graph on $13$ vertices with no triangle whose complement has no $5$-clique, and every graph on $14$ vertices has a triangle or its complement has a $5$-clique. Hence $R(3,5)=14$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib

theorem KernelRamsey.exact_35 :
    (∃ G : SimpleGraph (Fin 13), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 5) ∧
    ∀ G : SimpleGraph (Fin 14), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 5) := by sorry
