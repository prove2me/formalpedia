-- Prove2me | Theorems.Thm_GlobalTheory_GenTorsor_res_pb
-- name    : GlobalTheory.GenTorsor.res_pb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:49.189336+00:00
-- url     : https://prove2.me/theorems/dee2f54d-3960-4cb1-9abf-0f417a717222
-- title:
--   Gen Torsor: res pb
-- statement:
--   The Gen Torsor construction uses the res pb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L40-L43

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

theorem GlobalTheory.GenTorsor.res_pb (a : Y ⟶ X) {U : X.Opens} {V W : Y.Opens}
    (h : V ≤ a ⁻¹ᵁ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (pb a U V h x) = pb a U W (le_trans h' h) x := by sorry
