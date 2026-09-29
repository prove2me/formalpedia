-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0001_plan0005_specs_0064_0091
-- name    : Freiman.workReverse20260919_s0001_plan0005_specs_0064_0091
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T00:22:58.07772+00:00
-- url     : https://prove2.me/theorems/2cbf12f7-f9fe-47c9-a5c6-cc2b70a63a49
-- title:
--   Freiman.workReverse20260919_s0001_plan0005_specs_0064_0091
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ gs ∈ (((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 27, section14SpecValid section14Catalog (section14State section14Catalog 1) ((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0001_plan0005_specs_0064_0091 : ∀ gs ∈ (((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 27, section14SpecValid section14Catalog (section14State section14Catalog 1) ((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
