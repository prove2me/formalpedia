-- Prove2me | Theorems.Thm_MilnorDynamics_julia_set_iterate_eq
-- name    : MilnorDynamics.julia_set_iterate_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T12:13:27.987934+00:00
-- url     : https://prove2.me/theorems/b3cae3da-9256-4b82-a542-9865dead9e06
-- title:
--   Lemma 4.4 (Iteration Lemma) — $J(f^{\circ k})=J(f)$
-- statement:
--   Let $f$ be a rational map of the Riemann sphere $\hat{\mathbb C}$ of degree $d\ge 1$ (a nonconstant holomorphic self-map of $\hat{\mathbb C}$), and let $f^{\circ k}$ denote its $k$-fold iterate. For every $k>0$ the Julia set of the iterate coincides with the Julia set of $f$:
--
--   $$J\bigl(f^{\circ k}\bigr)=J(f).$$
--
--   This allows one to replace $f$ by an iterate in questions about the Julia set, e.g. to reduce statements about periodic points to statements about fixed points.
--
--   **Formalization Note** Milnor states the lemma for a nonconstant holomorphic self-map of a compact Riemann surface; for $S=\hat{\mathbb C}$ these are exactly the rational maps of degree $\ge1$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §4, p. 44, Lemma 4.4 (Iteration Lemma), for S the Riemann sphere

import Mathlib
import Definitions.Def_MilnorDynamics_RationalMaps

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem julia_set_iterate_eq (f : RationalMap) (hf : 1 ≤ f.degree) (k : ℕ) (hk : 0 < k) :
    juliaSet (f.toFun^[k]) = juliaSet f.toFun := by sorry

end MilnorDynamics
