-- Prove2me | Theorems.Thm_Freiman_section14_s0008_plan0004_specs_0064_0070
-- name    : Freiman.section14_s0008_plan0004_specs_0064_0070
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T06:22:24.367299+00:00
-- url     : https://prove2.me/theorems/db926ef2-2a5c-476a-9bf4-1a13a6d0e62d
-- title:
--   Freiman.section14_s0008_plan0004_specs_0064_0070
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 8).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 6, section14SpecValid section14Catalog (section14State section14Catalog 8) ((section14State section14Catalog 8).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0008_plan0004_specs_0064_0070 : ∀ gs ∈ (((section14State section14Catalog 8).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 6, section14SpecValid section14Catalog (section14State section14Catalog 8) ((section14State section14Catalog 8).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
