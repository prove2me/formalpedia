-- Prove2me | Theorems.Thm_Freiman_section14_s0015_plan0003_specs_all
-- name    : Freiman.section14_s0015_plan0003_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T21:28:53.22715+00:00
-- url     : https://prove2.me/theorems/5ddd3db9-a960-4ab3-8800-6bdad98e91f3
-- title:
--   Freiman.section14_s0015_plan0003_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 15).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0015_plan0003_specs_all : ∀ gs ∈ ((section14State section14Catalog 15).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
