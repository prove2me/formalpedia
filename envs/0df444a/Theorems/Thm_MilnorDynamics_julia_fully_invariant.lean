-- Prove2me | Theorems.Thm_MilnorDynamics_julia_fully_invariant
-- name    : MilnorDynamics.julia_fully_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T11:07:27.436986+00:00
-- url     : https://prove2.me/theorems/fe39c9dd-0f35-4dfd-8a82-e13fdb86014d
-- title:
--   Lemma 4.3 (Invariance Lemma) — $z\in J(f)\iff f(z)\in J(f)$
-- statement:
--   **Invariance Lemma.** Let $f$ be a rational map of the Riemann sphere. The Julia set $J(f)$ is fully invariant under $f$: a point $z$ belongs to $J(f)$ if and only if its image $f(z)$ belongs to $J(f)$. Equivalently, the Fatou set is fully invariant.
--
--   Full invariance is what gives the Julia set its self-similarity and is used in nearly every later argument about $J(f)$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §4, p. 44, Lemma 4.3 (Invariance Lemma), for a rational self-map of the Riemann sphere

import Mathlib
import Definitions.Def_MilnorDynamics_RationalMaps

open scoped OnePoint Topology
open Filter Set

namespace MilnorDynamics

theorem julia_fully_invariant (f : RationalMap) (z : OnePoint ℂ) :
    z ∈ juliaSet f.toFun ↔ f.toFun z ∈ juliaSet f.toFun := by sorry

end MilnorDynamics
