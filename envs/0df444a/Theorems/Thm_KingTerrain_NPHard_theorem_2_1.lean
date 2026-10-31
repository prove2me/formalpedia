-- Prove2me | Theorems.Thm_KingTerrain_NPHard_theorem_2_1
-- name    : KingTerrain.NPHard.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T23:52:29.135317+00:00
-- url     : https://prove2.me/theorems/549cad32-d9b4-4d3c-9a7c-10a3e3455fb2
-- title:
--   Theorem 2.1 — PLANAR 3-SAT is NP-complete
-- statement:
--   A planar 3-CNF formula has a planar formula graph consisting of its signed variable-clause incidences together with a cycle through the variables. Let $L_{\mathrm{P3SAT}}$ be the binary language of such formulas that have a satisfying Boolean assignment. Then
--
--   $$L_{\mathrm{P3SAT}}\in\mathrm{NP}\quad\text{and}\quad
--     \forall K\in\mathrm{NP},\ K\le_p L_{\mathrm{P3SAT}}.$$
--
--   Reductions are polynomial-time many-one reductions with finite-machine semantics, over every finite nonempty source alphabet. This is the NP-completeness result attributed to Lichtenstein in the source and used as the reduction's starting problem. It assumes neither a given reduction nor SAT-hardness as a premise.
--
--   Differences from the source:
--   - encoding: Boolean 3-CNF and its variable cycle → finite signed clause lists with three occurrences per clause and zero-based variable labels specifying cycle order; reason: makes the source formula graph explicit, with the simple-graph convention for fewer than three variables
--   - encoding: decision problem on formulas → canonical self-delimiting binary formula codes rejecting malformed words; reason: supplies a finite-string representation without polarity or embedding promises
--   - encoding: NP-complete → the published CookPvsNP.NPComplete predicate; reason: expresses both membership and universal polynomial-time many-one hardness using finite machines
-- source:
--   King and Krohn, Terrain Guarding is NP-Hard, DOI 10.1137/100791506, supplied PDF dated October 20, 2009, PDF p.2, Theorem 2.1 (Lichtenstein [14] Theorem 2).

import Definitions.Def_KingTerrain_NPHard_PlanarSAT

set_option autoImplicit false

namespace KingTerrain.NPHard

theorem theorem_2_1 : CookPvsNP.NPComplete planarSATLanguage := by sorry

end KingTerrain.NPHard
