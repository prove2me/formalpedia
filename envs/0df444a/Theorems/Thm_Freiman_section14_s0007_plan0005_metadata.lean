-- Prove2me | Theorems.Thm_Freiman_section14_s0007_plan0005_metadata
-- name    : Freiman.section14_s0007_plan0005_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:56:36.958878+00:00
-- url     : https://prove2.me/theorems/37f8ea91-8f92-4b0e-b503-879276e226a1
-- title:
--   Freiman.section14_s0007_plan0005_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ≠ [] ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).first = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).second = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).caseId = ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).extra = [] ∧ (((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.map Prod.snd).toFinset = (section14ExpectedSpecs ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).targetLower).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_plan0005_metadata : ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ≠ [] ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).first = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).second = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).caseId = ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).extra = [] ∧ (((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.map Prod.snd).toFinset = (section14ExpectedSpecs ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).targetLower).toFinset := by sorry
