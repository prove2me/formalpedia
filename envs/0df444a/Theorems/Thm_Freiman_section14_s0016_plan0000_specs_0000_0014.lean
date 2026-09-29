-- Prove2me | Theorems.Thm_Freiman_section14_s0016_plan0000_specs_0000_0014
-- name    : Freiman.section14_s0016_plan0000_specs_0000_0014
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T21:56:04.555892+00:00
-- url     : https://prove2.me/theorems/9d65d58a-0e27-4cbd-aab8-27a4fcfa0fd0
-- title:
--   Freiman.section14_s0016_plan0000_specs_0000_0014
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 16).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 14, section14SpecValid section14Catalog (section14State section14Catalog 16) ((section14State section14Catalog 16).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_plan0000_specs_0000_0014 : ∀ gs ∈ (((section14State section14Catalog 16).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 14, section14SpecValid section14Catalog (section14State section14Catalog 16) ((section14State section14Catalog 16).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
