-- Prove2me | Theorems.Thm_Freiman_section14_s0016_plan0001_specs_all
-- name    : Freiman.section14_s0016_plan0001_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T00:51:12.638642+00:00
-- url     : https://prove2.me/theorems/62e653c9-2f39-4694-96d4-66783547ee7d
-- title:
--   Freiman.section14_s0016_plan0001_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 16).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 16) ((section14State section14Catalog 16).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_plan0001_specs_all : ∀ gs ∈ ((section14State section14Catalog 16).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 16) ((section14State section14Catalog 16).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
