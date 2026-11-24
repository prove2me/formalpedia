-- Prove2me | Theorems.Thm_KernelRamsey_exact_44
-- name    : KernelRamsey.exact_44
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:27:52.508013+00:00
-- url     : https://prove2.me/theorems/06ed4663-543b-4f42-b49f-6654c000c7bb
-- title:
--   The exact value $R(4,4)=18$
-- statement:
--   There is a graph on $17$ vertices with no $4$-clique whose complement has no $4$-clique, and every graph on $18$ vertices has a $4$-clique or its complement has a $4$-clique. Hence $R(4,4)=18$.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib

theorem KernelRamsey.exact_44 :
    (∃ G : SimpleGraph (Fin 17), G.CliqueFree 4 ∧ Gᶜ.CliqueFree 4) ∧
    ∀ G : SimpleGraph (Fin 18), ¬ (G.CliqueFree 4 ∧ Gᶜ.CliqueFree 4) := by sorry
