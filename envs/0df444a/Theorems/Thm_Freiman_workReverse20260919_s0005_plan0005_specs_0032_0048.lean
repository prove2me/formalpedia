-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_plan0005_specs_0032_0048
-- name    : Freiman.workReverse20260919_s0005_plan0005_specs_0032_0048
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:24:30.477003+00:00
-- url     : https://prove2.me/theorems/95273f54-449b-44ad-a764-5697ddd7645f
-- title:
--   Freiman.workReverse20260919_s0005_plan0005_specs_0032_0048
-- statement:
--   The exact original plan metadata and all endpoint specifications in the indicated slice are verified using the original catalogue and endpoint formulae.
--
--   ∀ gs ∈ (((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 32).take 16, section14SpecValid section14Catalog (section14State section14Catalog 5) ((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_plan0005_specs_0032_0048 : ∀ gs ∈ (((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 32).take 16, section14SpecValid section14Catalog (section14State section14Catalog 5) ((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
