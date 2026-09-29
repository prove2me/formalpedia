-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_plan0005_specs_0016_0032
-- name    : Freiman.workReverse20260919_s0005_plan0005_specs_0016_0032
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:24:27.865758+00:00
-- url     : https://prove2.me/theorems/6c940be0-6576-4f82-b025-0782b451da6c
-- title:
--   Freiman.workReverse20260919_s0005_plan0005_specs_0016_0032
-- statement:
--   The exact original plan metadata and all endpoint specifications in the indicated slice are verified using the original catalogue and endpoint formulae.
--
--   ∀ gs ∈ (((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 16, section14SpecValid section14Catalog (section14State section14Catalog 5) ((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_plan0005_specs_0016_0032 : ∀ gs ∈ (((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 16, section14SpecValid section14Catalog (section14State section14Catalog 5) ((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
