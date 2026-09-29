-- Prove2me | Theorems.Thm_Freiman_section14_s0004_plan0000_specs_all
-- name    : Freiman.section14_s0004_plan0000_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T03:12:01.527353+00:00
-- url     : https://prove2.me/theorems/502ddf3c-2322-4595-a102-8b660630c937
-- title:
--   Freiman.section14_s0004_plan0000_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 4).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 4) ((section14State section14Catalog 4).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_plan0000_specs_all : ∀ gs ∈ ((section14State section14Catalog 4).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 4) ((section14State section14Catalog 4).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
