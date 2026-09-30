-- Prove2me | Theorems.Thm_MilnorDynamics_julia_set_nonempty
-- name    : MilnorDynamics.julia_set_nonempty
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T12:44:00.416689+00:00
-- url     : https://prove2.me/theorems/0b70fa47-177f-4095-a051-474c7e9f0262
-- title:
--   Lemma 4.8 — the Julia set of a rational map of degree $\ge 2$ is nonempty
-- statement:
--   Let $f$ be a rational map of the Riemann sphere of degree $d\ge 2$. Then its Julia set is nonvacuous:
--
--   $$J(f)\neq\emptyset.$$
--
--   The hypothesis $d\ge2$ is necessary: a Möbius transformation such as $z\mapsto 2z$ or $z\mapsto z+1$ has empty Julia set. This lemma is the starting point for all structural results about $J(f)$ (perfectness, density of preimages and of repelling cycles).
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §4, p. 46, Lemma 4.8 (J Is not Empty)

import Mathlib
import Definitions.Def_MilnorDynamics_RationalMaps

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem julia_set_nonempty (f : RationalMap) (hf : 2 ≤ f.degree) :
    (juliaSet f.toFun).Nonempty := by sorry

end MilnorDynamics
