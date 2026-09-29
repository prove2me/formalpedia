-- Prove2me | Theorems.Thm_Freiman_section14_s0011_plan0002_specs_0016_0021
-- name    : Freiman.section14_s0011_plan0002_specs_0016_0021
-- status  : Proved
-- author  : @tp
-- created : 2026-09-18T11:36:34.173239+00:00
-- url     : https://prove2.me/theorems/5c93e31e-67d3-4e9b-a643-00a461ccd30b
-- title:
--   Freiman.section14_s0011_plan0002_specs_0016_0021
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ∀ gs ∈ (((section14State section14Catalog 11).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 5, section14SpecValid section14Catalog (section14State section14Catalog 11) ((section14State section14Catalog 11).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0011_plan0002_specs_0016_0021 : ∀ gs ∈ (((section14State section14Catalog 11).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 5, section14SpecValid section14Catalog (section14State section14Catalog 11) ((section14State section14Catalog 11).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
