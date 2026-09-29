-- Prove2me | Theorems.Thm_Freiman_section14_s0004_plan0002_specs_0016_0021
-- name    : Freiman.section14_s0004_plan0002_specs_0016_0021
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T01:32:24.966222+00:00
-- url     : https://prove2.me/theorems/909a00fa-ecde-4ab0-b2de-8e1149b4ed4b
-- title:
--   Freiman.section14_s0004_plan0002_specs_0016_0021
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 4).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 5, section14SpecValid section14Catalog (section14State section14Catalog 4) ((section14State section14Catalog 4).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_plan0002_specs_0016_0021 : ∀ gs ∈ (((section14State section14Catalog 4).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 5, section14SpecValid section14Catalog (section14State section14Catalog 4) ((section14State section14Catalog 4).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
