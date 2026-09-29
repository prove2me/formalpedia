-- Prove2me | Theorems.Thm_MilnorDynamics_fixed_points_card_le
-- name    : MilnorDynamics.fixed_points_card_le
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T11:08:09.258767+00:00
-- url     : https://prove2.me/theorems/81a18185-2768-40b4-bc9a-f19b9806d1cd
-- title:
--   Lemma 12.1 (consequence) — a rational map other than the identity has at most $d+1$ fixed points
-- statement:
--   Milnor's Lemma 12.1: *if $f$ is not the identity map, then $f$ has exactly $d+1$ fixed points, counted with multiplicity.* The milestone records the consequence that the set of fixed points of a rational map $f\neq\mathrm{id}$ of degree $d$ on $\hat{\mathbb C}$ is finite with at most $d+1$ elements.
--
--   **Formalization Note** Multiplicities are not formalized; only the resulting upper bound on the number of distinct fixed points is stated.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §12, p. 142, Lemma 12.1 (the counting-with-multiplicity statement is weakened to an upper bound on distinct fixed points)

import Mathlib
import Definitions.Def_MilnorDynamics_PeriodicPoints

open scoped OnePoint Topology
open Filter Set

namespace MilnorDynamics

theorem fixed_points_card_le (f : RationalMap) (hf : f.toFun ≠ id) :
    (Function.fixedPoints f.toFun).Finite ∧
      (Function.fixedPoints f.toFun).ncard ≤ f.degree + 1 := by sorry

end MilnorDynamics
