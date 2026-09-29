-- Prove2me | Theorems.Thm_MilnorDynamics_julia_eq_closure_repelling
-- name    : MilnorDynamics.julia_eq_closure_repelling
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T12:46:05.436982+00:00
-- url     : https://prove2.me/theorems/fcf06312-63a8-4658-a176-719c639b3c32
-- title:
--   Theorem 14.1 — the Julia set is the closure of the repelling periodic points
-- statement:
--   Let $f$ be a rational map of the Riemann sphere of degree $d\ge 2$. A periodic point $z_0$ of minimal period $m$ is **repelling** if its multiplier $\lambda=(f^{\circ m})'(z_0)$ (computed in a local coordinate) satisfies $|\lambda|>1$. Then the Julia set is equal to the closure of the set of repelling periodic points:
--
--   $$J(f)=\overline{\{z_0\in\hat{\mathbb C} : z_0 \text{ is a repelling periodic point of } f\}}.$$
--
--   This theorem of Fatou and Julia identifies the Fatou-style definition of $J(f)$ (the locus of non-normality) with Julia's original definition, and is the main tool for showing that $J(f)$ is the locus of chaotic dynamics.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §14, p. 156, Theorem 14.1

import Mathlib
import Definitions.Def_MilnorDynamics_PeriodicPoints

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem julia_eq_closure_repelling (f : RationalMap) (hf : 2 ≤ f.degree) :
    juliaSet f.toFun = closure (repellingPeriodicPts f.toFun) := by sorry

end MilnorDynamics
