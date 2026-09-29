-- Prove2me | Theorems.Thm_Freiman_section14_s0014_plan0000_specs_all
-- name    : Freiman.section14_s0014_plan0000_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T03:04:01.149844+00:00
-- url     : https://prove2.me/theorems/78d8832a-047a-453f-9098-99323b444619
-- title:
--   Freiman.section14_s0014_plan0000_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 14).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0014_plan0000_specs_all : ∀ gs ∈ ((section14State section14Catalog 14).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 14) ((section14State section14Catalog 14).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
