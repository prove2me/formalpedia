-- Prove2me | Theorems.Thm_GlobalTheory_GenTorsor_unit_ext_cover
-- name    : GlobalTheory.GenTorsor.unit_ext_cover
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:50.341779+00:00
-- url     : https://prove2.me/theorems/9d419113-c1ea-4c66-81c7-0a1e6532cfde
-- title:
--   Gen Torsor: unit ext cover
-- statement:
--   The Gen Torsor construction uses the unit ext cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L105-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L105-L110

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
variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]

theorem GlobalTheory.GenTorsor.unit_ext_cover (hc : ∀ x : X, ∃ i y, a i y = x) {V : X.Opens} {u v : Γ(X, V)ˣ}
    (h : ∀ i, pb (a i) V _ le_rfl u = pb (a i) V _ le_rfl v) : u = v := by sorry
