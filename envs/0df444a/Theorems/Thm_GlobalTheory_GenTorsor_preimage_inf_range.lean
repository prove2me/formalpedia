-- Prove2me | Theorems.Thm_GlobalTheory_GenTorsor_preimage_inf_range
-- name    : GlobalTheory.GenTorsor.preimage_inf_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:36.457601+00:00
-- url     : https://prove2.me/theorems/6cc5e7d0-ee59-4620-a54a-332ec3531782
-- title:
--   Gen Torsor: preimage inf range
-- statement:
--   The Gen Torsor construction uses the preimage inf range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L100-L103

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

theorem GlobalTheory.GenTorsor.preimage_inf_range (i : J) (V : X.Opens) :
    a i ⁻¹ᵁ V = a i ⁻¹ᵁ (V ⊓ (a i).opensRange) := by sorry
