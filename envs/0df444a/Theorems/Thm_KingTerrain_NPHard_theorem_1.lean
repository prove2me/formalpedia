-- Prove2me | Theorems.Thm_KingTerrain_NPHard_theorem_1
-- name    : KingTerrain.NPHard.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T23:53:33.664518+00:00
-- url     : https://prove2.me/theorems/a1d50bec-553a-48ba-bb12-1cc50419997f
-- title:
--   Theorem 1 — Discrete and continuous terrain guarding are NP-hard
-- statement:
--   A terrain is a nonempty finite polygonal chain in the real plane with strictly increasing vertex horizontal coordinates. Two terrain points see each other when their closed connecting segment never lies strictly below the terrain. A guarding covers every real point of the terrain. Discrete guards must be listed vertices; continuous guards may be arbitrary real points of the carrier.
--
--   Let $L_{\mathrm{disc}}$ and $L_{\mathrm{cont}}$ be the budget decision languages for these two variants, using exact rational input coordinates and a natural budget. Then
--
--   $$\mathrm{NPHard}(L_{\mathrm{disc}})\ \land\ \mathrm{NPHard}(L_{\mathrm{cont}}).$$
--
--   Each hardness assertion ranges over every language in NP over every finite nonempty alphabet, requiring a finite-machine polynomial-time many-one reduction with an equivalence on all inputs. Both claims are unconditional. No reduction correctness, polynomial coordinate realization, or planar-SAT hardness is assumed as a premise. The continuous assertion does not claim membership in NP. This is the source's main decision-hardness result for the minimum terrain guarding problem.
--
--   Differences from the source:
--   - encoding: finitely described terrain and guard budget → canonical binary codes of exact rational vertices and a natural budget; reason: makes finite input length, including every coordinate bit, explicit while guard locations and covered points remain real
--   - encoding: strictly x-ordered polygonal chain → a chain with n edges and n+1 real vertices subject to strict horizontal order and closed-segment visibility; reason: fixes finite indexing and preserves singleton chains, horizontal edges and boundary contact
--   - encoding: minimum terrain guarding is NP-hard for both standard variants → conjunction of universal many-one NP-hardness of their budget decision languages; reason: follows the decision version and both variants specified in the abstract and pp.1–2, using finite-machine polynomial time
-- source:
--   King and Krohn, Terrain Guarding is NP-Hard, DOI 10.1137/100791506, supplied PDF dated October 20, 2009, PDF p.2, Theorem 1, with the model and scope on pp.1–2.

import Definitions.Def_KingTerrain_NPHard_Languages

set_option autoImplicit false

namespace KingTerrain.NPHard

theorem theorem_1 :
    IsNPHard discreteTerrainLanguage ∧ IsNPHard continuousTerrainLanguage := by sorry

end KingTerrain.NPHard
