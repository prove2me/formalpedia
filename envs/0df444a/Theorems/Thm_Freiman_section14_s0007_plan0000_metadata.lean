-- Prove2me | Theorems.Thm_Freiman_section14_s0007_plan0000_metadata
-- name    : Freiman.section14_s0007_plan0000_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-09-19T08:42:31.911495+00:00
-- url     : https://prove2.me/theorems/92fbdd8f-7b71-4f7a-84e3-928fe933772e
-- title:
--   Freiman.section14_s0007_plan0000_metadata
-- statement:
--   Exact auxiliary assertion from Freiman section 14. ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ≠ [] ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).first = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).second = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).caseId = ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).extra = [] ∧ (((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.map Prod.snd).toFinset = (section14ExpectedSpecs ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).targetLower).toFinset
-- source:
--   Exact finite subclaim supporting the original section14StateValid targets in Freiman M7.

import Definitions.Def_Freiman_section14Data
open Freiman

theorem Freiman.section14_s0007_plan0000_metadata : ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ≠ [] ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).first = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).second = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).caseId = ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId ∧ (section14Goal section14Catalog ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).extra = [] ∧ (((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.map Prod.snd).toFinset = (section14ExpectedSpecs ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ((section14State section14Catalog 7).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).targetLower).toFinset := by sorry
