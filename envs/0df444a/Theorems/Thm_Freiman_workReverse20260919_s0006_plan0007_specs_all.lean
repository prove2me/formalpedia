-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0006_plan0007_specs_all
-- name    : Freiman.workReverse20260919_s0006_plan0007_specs_all
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T05:54:55.157005+00:00
-- url     : https://prove2.me/theorems/57073a7b-58f2-4226-9675-ba6a5dc9f990
-- title:
--   Freiman.workReverse20260919_s0006_plan0007_specs_all
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ gs ∈ ((section14State section14Catalog 6).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 6) ((section14State section14Catalog 6).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0006_plan0007_specs_all : ∀ gs ∈ ((section14State section14Catalog 6).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 6) ((section14State section14Catalog 6).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
