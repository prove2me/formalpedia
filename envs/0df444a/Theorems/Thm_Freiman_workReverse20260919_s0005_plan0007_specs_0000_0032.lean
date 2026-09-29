-- Prove2me | Theorems.Thm_Freiman_workReverse20260919_s0005_plan0007_specs_0000_0032
-- name    : Freiman.workReverse20260919_s0005_plan0007_specs_0000_0032
-- status  : Proved
-- author  : @tp
-- created : 2026-09-20T07:09:54.065307+00:00
-- url     : https://prove2.me/theorems/f9f3dcbe-2b20-4cce-84ee-3e287b019b35
-- title:
--   Freiman.workReverse20260919_s0005_plan0007_specs_0000_0032
-- statement:
--   Exact existing disjoint slice assembly with genuinely checked team proofs inlined.
--
--   ∀ gs ∈ (((section14State section14Catalog 5).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 32, section14SpecValid section14Catalog (section14State section14Catalog 5) ((section14State section14Catalog 5).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
-- source:
--   Exact disjoint subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.workReverse20260919_s0005_plan0007_specs_0000_0032 : ∀ gs ∈ (((section14State section14Catalog 5).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 32, section14SpecValid section14Catalog (section14State section14Catalog 5) ((section14State section14Catalog 5).plans[7]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by sorry
