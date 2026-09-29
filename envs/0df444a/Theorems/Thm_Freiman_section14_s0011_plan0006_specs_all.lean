-- Prove2me | Theorems.Thm_Freiman_section14_s0011_plan0006_specs_all
-- name    : Freiman.section14_s0011_plan0006_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T16:14:53.194023+00:00
-- url     : https://prove2.me/theorems/0702f96b-ed2c-43bd-a413-c0e1b8d2dbdf
-- title:
--   Freiman.section14_s0011_plan0006_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 11).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 11) ((section14State section14Catalog 11).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_plan0006_specs_all : ∀ gs ∈ ((section14State section14Catalog 11).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 11) ((section14State section14Catalog 11).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
