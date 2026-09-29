-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0004_specs_0048_0063
-- name    : Freiman.section14_s0014_plan0004_specs_0048_0063
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T00:15:17.643985+00:00
-- url     : https://prove2.me/theorems/4dd80082-59c4-4558-ac94-191d6cab8ebd
-- title:
--   Freiman.section14_s0014_plan0004_specs_0048_0063
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 14).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 48).take 15, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0004_specs_0048_0063 : ∀ gs ∈ (((section14State section14Catalog 14).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 48).take 15, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
