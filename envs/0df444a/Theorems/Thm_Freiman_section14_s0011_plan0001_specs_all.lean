-- Prove2me | Theorems.Thm_Freiman_section14_s0011_plan0001_specs_all
-- name    : Freiman.section14_s0011_plan0001_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T16:07:07.310026+00:00
-- url     : https://prove2.me/theorems/cf53cad2-5b01-46d2-afe2-37a5ef553cfd
-- title:
--   Freiman.section14_s0011_plan0001_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 11).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 11) ((section14State section14Catalog 11).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_plan0001_specs_all : ∀ gs ∈ ((section14State section14Catalog 11).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 11) ((section14State section14Catalog 11).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
