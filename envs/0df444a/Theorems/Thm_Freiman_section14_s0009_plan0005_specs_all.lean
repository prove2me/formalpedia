-- Prove2me | Theorems.Thm_Freiman_section14_s0009_plan0005_specs_all
-- name    : Freiman.section14_s0009_plan0005_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T22:27:08.586336+00:00
-- url     : https://prove2.me/theorems/f5ea6c76-8a48-4670-85af-847126018dfd
-- title:
--   Freiman.section14_s0009_plan0005_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 9).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 9) ((section14State section14Catalog 9).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0009_plan0005_specs_all : ∀ gs ∈ ((section14State section14Catalog 9).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 9) ((section14State section14Catalog 9).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
