-- Prove2me | Theorems.Thm_GlobalTheory_GenTorsor_pb_res
-- name    : GlobalTheory.GenTorsor.pb_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:05.827798+00:00
-- url     : https://prove2.me/theorems/91056baa-845e-4c89-8a55-1eee3e5fdc8c
-- title:
--   Gen Torsor: pb res
-- statement:
--   The Gen Torsor construction uses the pb res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L45-L48

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

theorem GlobalTheory.GenTorsor.pb_res (a : Y ⟶ X) {U V : X.Opens} {W : Y.Opens}
    (h : V ≤ U) (h' : W ≤ a ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    pb a V W h' (res h x) = pb a U W (h'.trans (a.preimage_mono h)) x := by sorry
