-- Prove2me | Theorems.Thm_GlobalTheory_GenTorsor_pb_pb
-- name    : GlobalTheory.GenTorsor.pb_pb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:39.800213+00:00
-- url     : https://prove2.me/theorems/75704b0e-f74a-4d0f-9dbe-72d961761142
-- title:
--   Gen Torsor: pb pb
-- statement:
--   The Gen Torsor construction uses the pb pb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L16-L22

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

theorem GlobalTheory.GenTorsor.pb_pb (b : Z ⟶ Y) (a : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (h : V ≤ a ⁻¹ᵁ U) (h' : W ≤ b ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    pb b V W h' (pb a U V h x) = pb (b ≫ a) U W (h'.trans (b.preimage_mono h)) x := by sorry
