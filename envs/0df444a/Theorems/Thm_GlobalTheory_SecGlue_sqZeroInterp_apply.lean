-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_sqZeroInterp_apply
-- name    : GlobalTheory.SecGlue.sqZeroInterp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:17.636314+00:00
-- url     : https://prove2.me/theorems/5b94ec6e-eb52-4e3b-a3f7-bca3d3862f3b
-- title:
--   Sec Glue: sq Zero Interp apply
-- statement:
--   The Sec Glue construction uses the sq Zero Interp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSqZeroExtendLocalizationAwayPow.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSqZeroExtendLocalizationAwayPow.lean#L25-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue

theorem GlobalTheory.SecGlue.sqZeroInterp_apply {R B S : Type} [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] (J : Ideal S) (hJ : J ^ 2 = ⊥) (α β : B →ₐ[R] S)
    (h : ∀ x, β x - α x ∈ J) (c : S) (x : B) :
    sqZeroInterp J hJ α β h c x = α x + c * (β x - α x) := by sorry

attribute [defeq] GlobalTheory.SecGlue.sqZeroInterp_apply
