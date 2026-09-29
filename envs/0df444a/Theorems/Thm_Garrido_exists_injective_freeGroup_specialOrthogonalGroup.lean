-- Prove2me | Theorems.Thm_Garrido_exists_injective_freeGroup_specialOrthogonalGroup
-- name    : Garrido.exists_injective_freeGroup_specialOrthogonalGroup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-24T13:59:59.476743+00:00
-- url     : https://prove2.me/theorems/88beee78-4a07-49c2-a2bb-7140e1d95967
-- title:
--   Proposition 1.6 — SO(3,ℝ) contains a free group of rank two
-- statement:
--   There is an injective group homomorphism from the free group $F_2$ on two generators
--   into the rotation group $SO(3,\mathbb{R})$:
--
--   $$\exists\, f : F_2 \hookrightarrow SO(3,\mathbb{R}).$$
--
--   It is the only group-theoretic fact about rotations that the Banach–Tarski paradox needs.
--
--   **Formalization Note.** $F_2$ is `FreeGroup (Fin 2)` and $SO(3,\mathbb{R})$ is
--   `Matrix.specialOrthogonalGroup (Fin 3) ℝ`, the real $3 \times 3$ matrices $A$ with
--   $A^{\mathsf T} A = 1$ and $\det A = 1$.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 2, Proposition 1.6; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib

namespace Garrido

theorem exists_injective_freeGroup_specialOrthogonalGroup :
    ∃ f : FreeGroup (Fin 2) →* Matrix.specialOrthogonalGroup (Fin 3) ℝ, Function.Injective f := by
  sorry

end Garrido
