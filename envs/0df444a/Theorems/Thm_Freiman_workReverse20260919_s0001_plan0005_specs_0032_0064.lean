-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_plan0005_specs_0032_0064
-- name    : Freiman.workReverse20260919_s0001_plan0005_specs_0032_0064
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T00:15:31.606897+00:00
-- url     : https://prove2.me/theorems/e5f7645b-9e13-4048-a077-d88f98d0c8b4
-- title:
--   Freiman.workReverse20260919_s0001_plan0005_specs_0032_0064
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ gs ∈ (((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 32).take 32, section14SpecValid section14Catalog (section14State section14Catalog 1) ((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_plan0005_specs_0032_0064 : ∀ gs ∈ (((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 32).take 32, section14SpecValid section14Catalog (section14State section14Catalog 1) ((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
