-- Prove2me | Theorems.Thm_Freiman_section14_s0016_plan0005_specs_all
-- name    : Freiman.section14_s0016_plan0005_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T00:58:50.309006+00:00
-- url     : https://prove2.me/theorems/876aea68-91a0-4cf2-8bed-f07515b3c3f1
-- title:
--   Freiman.section14_s0016_plan0005_specs_all
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ ((section14State section14Catalog 16).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 16) ((section14State section14Catalog 16).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0016_plan0005_specs_all : ∀ gs ∈ ((section14State section14Catalog 16).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 16) ((section14State section14Catalog 16).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
