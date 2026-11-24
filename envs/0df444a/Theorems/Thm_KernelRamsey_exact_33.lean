-- Prove2me | Theorems.Thm_KernelRamsey_exact_33
-- name    : KernelRamsey.exact_33
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:27:31.481335+00:00
-- url     : https://prove2.me/theorems/0c28523d-2ab3-461d-a94d-f38e4f06525c
-- title:
--   The exact value $R(3,3)=6$
-- statement:
--   There is a graph on $5$ vertices with no triangle whose complement has no triangle, and every graph on $6$ vertices has a triangle or its complement has a triangle. Hence $R(3,3)=6$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib

theorem KernelRamsey.exact_33 :
    (∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3) ∧
    ∀ G : SimpleGraph (Fin 6), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3) := by sorry
