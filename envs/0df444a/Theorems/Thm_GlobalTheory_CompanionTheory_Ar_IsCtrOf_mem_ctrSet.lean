-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_IsCtrOf_mem_ctrSet
-- name    : GlobalTheory.CompanionTheory.Ar.IsCtrOf.mem_ctrSet
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:21.136371+00:00
-- url     : https://prove2.me/theorems/b4d668a7-1063-4aa9-a6bc-faf5b12df98f
-- title:
--   Is Ctr Of: mem ctr Set
-- statement:
--   The Is Ctr Of construction uses the mem ctr Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L133-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L133-L136

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory
variable {X X' X'' : Scheme.{0}} {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω'']
  {E F : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F]
variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
  {ξ'' : Spec (CommRingCat.of Ω'') ⟶ X''}

theorem GlobalTheory.CompanionTheory.Ar.IsCtrOf.mem_ctrSet {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω} {M : PModel o x}
    {i : Ω →+* Ω'} {p : Cpt M.ξ} {p' : Cpt ξ'} (h : IsCtrOf i p p') : p' ∈ ctrSet o x i ξ' := by sorry
