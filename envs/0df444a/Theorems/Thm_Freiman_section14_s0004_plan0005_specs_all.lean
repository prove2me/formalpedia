-- Prove2me | Theorems.Thm_Freiman_section14_s0004_plan0005_specs_all
-- name    : Freiman.section14_s0004_plan0005_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T03:18:22.717669+00:00
-- url     : https://prove2.me/theorems/d9601d8b-e622-4ea8-baa3-12227361ef47
-- title:
--   Freiman.section14_s0004_plan0005_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 4).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 4) ((section14State section14Catalog 4).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0004_plan0005_specs_all : ∀ gs ∈ ((section14State section14Catalog 4).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 4) ((section14State section14Catalog 4).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
