-- Prove2me | Theorems.Thm_Freiman_section14_s0009_plan0001_specs_all
-- name    : Freiman.section14_s0009_plan0001_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T22:13:32.398056+00:00
-- url     : https://prove2.me/theorems/da0efc25-47eb-487b-80be-c744d0108933
-- title:
--   Freiman.section14_s0009_plan0001_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 9).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 9) ((section14State section14Catalog 9).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_plan0001_specs_all : ∀ gs ∈ ((section14State section14Catalog 9).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 9) ((section14State section14Catalog 9).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
