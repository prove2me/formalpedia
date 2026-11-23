-- Prove2me | Theorems.Thm_GlobalTheory_GenTorsor_pb_bijective
-- name    : GlobalTheory.GenTorsor.pb_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:16.049683+00:00
-- url     : https://prove2.me/theorems/d4e73753-197b-46f3-bc17-7c98cf4a7d33
-- title:
--   Gen Torsor: pb bijective
-- statement:
--   The Gen Torsor construction uses the pb bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L52-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean#L52-L63

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

theorem GlobalTheory.GenTorsor.pb_bijective (a : Y ⟶ X) [IsOpenImmersion a] {U : X.Opens} (hU : U ≤ a.opensRange)
    {W : Y.Opens} (h : W = a ⁻¹ᵁ U) : Function.Bijective (pb a U W h.le) := by sorry
