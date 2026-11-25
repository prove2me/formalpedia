-- Prove2me | Theorems.Thm_GlobalTheory_GenTorsor_res_pullU
-- name    : GlobalTheory.GenTorsor.res_pullU
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:28.049732+00:00
-- url     : https://prove2.me/theorems/384932d9-1fe2-5bc1-9d62-65809116de46
-- title:
--   Gen Torsor: res pull U
-- statement:
--   The Gen Torsor construction uses the res pull U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L28-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenTorsor
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.GenTorsor.res_pullU (a : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (h : W ≤ a ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU a U x) = pb a U W h x := by sorry
