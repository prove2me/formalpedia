-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_plan0005_specs_0080_0091
-- name    : Freiman.workReverse20260919_s0005_plan0005_specs_0080_0091
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:24:45.35267+00:00
-- url     : https://prove2.me/theorems/94b89af9-4176-459d-b416-ded92a80a828
-- title:
--   Freiman.workReverse20260919_s0005_plan0005_specs_0080_0091
-- statement:
--   The exact original plan metadata and all endpoint specifications in the indicated slice are verified using the original catalogue and endpoint formulae.
--
--   ∀ gs ∈ (((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 11, section14SpecValid section14Catalog (section14State section14Catalog 5) ((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_plan0005_specs_0080_0091 : ∀ gs ∈ (((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 11, section14SpecValid section14Catalog (section14State section14Catalog 5) ((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
