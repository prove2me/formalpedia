-- Prove2me | Theorems.Thm_KernelRamsey_exact_34
-- name    : KernelRamsey.exact_34
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:27:45.179002+00:00
-- url     : https://prove2.me/theorems/d894e2b1-9c3e-4f09-89c5-a16e90928291
-- title:
--   The exact value $R(3,4)=9$
-- statement:
--   There is a graph on $8$ vertices with no triangle whose complement has no $4$-clique, and every graph on $9$ vertices has a triangle or its complement has a $4$-clique. Hence $R(3,4)=9$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib

theorem KernelRamsey.exact_34 :
    (∃ G : SimpleGraph (Fin 8), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 4) ∧
    ∀ G : SimpleGraph (Fin 9), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 4) := by sorry
