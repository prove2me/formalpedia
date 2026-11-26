-- Prove2me | Theorems.Thm_IsInjectiveSpace_pi
-- name    : IsInjectiveSpace.pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:51.433854+00:00
-- url     : https://prove2.me/theorems/0123cbf8-aa95-436f-b42f-543fc1ab8ddf
-- title:
--   Is Injective Space: pi
-- statement:
--   **Scott 1972, Proposition 1.3.** Products of injective spaces are injective.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L55-L62
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Injective.lean#L55-L62

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
set_option autoImplicit true
open Topology TopologicalSpace
universe u v w

theorem IsInjectiveSpace.pi {ι : Type w} (D : ι → Type v) [∀ i, TopologicalSpace (D i)]
    (h : ∀ i, IsInjectiveSpace.{u} (D i)) : IsInjectiveSpace.{u} (∀ i, D i) := by sorry
