-- Prove2me | Theorems.Thm_GlobalTheory_GenTorsor_le_iSup_range
-- name    : GlobalTheory.GenTorsor.le_iSup_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:57.392927+00:00
-- url     : https://prove2.me/theorems/ae30d2f1-5cf5-4ae8-bec9-75c3c95b1d71
-- title:
--   Gen Torsor: le i Sup range
-- statement:
--   The Gen Torsor construction uses the le i Sup range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L95-L98

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

theorem GlobalTheory.GenTorsor.le_iSup_range (hc : ∀ x : X, ∃ i y, a i y = x) (V : X.Opens) :
    V ≤ ⨆ i, V ⊓ (a i).opensRange := by sorry
