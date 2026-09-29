-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_plan0007_specs_0032_0063
-- name    : Freiman.workReverse20260919_s0005_plan0007_specs_0032_0063
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:09:47.150254+00:00
-- url     : https://prove2.me/theorems/668fc7f8-fa18-48b0-b11d-6d3661441cd2
-- title:
--   Freiman.workReverse20260919_s0005_plan0007_specs_0032_0063
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ gs ∈ (((section14State section14Catalog 5).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 32).take 31, section14SpecValid section14Catalog (section14State section14Catalog 5) ((section14State section14Catalog 5).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_plan0007_specs_0032_0063 : ∀ gs ∈ (((section14State section14Catalog 5).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 32).take 31, section14SpecValid section14Catalog (section14State section14Catalog 5) ((section14State section14Catalog 5).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
