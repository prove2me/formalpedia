-- Prove2me | Theorems.Thm_Freiman_section14_s0004_plan0003_specs_0000_0016
-- name    : Freiman.section14_s0004_plan0003_specs_0000_0016
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T01:34:14.907443+00:00
-- url     : https://prove2.me/theorems/6a845387-1813-4dd0-ad93-c22aa102df2a
-- title:
--   Freiman.section14_s0004_plan0003_specs_0000_0016
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 4).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 4) ((section14State section14Catalog 4).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_plan0003_specs_0000_0016 : ∀ gs ∈ (((section14State section14Catalog 4).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 4) ((section14State section14Catalog 4).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
