-- Prove2me | Theorems.Thm_GlobalTheory_AffGlue_secEquiv_resM
-- name    : GlobalTheory.AffGlue.secEquiv_resM
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:55:19.990476+00:00
-- url     : https://prove2.me/theorems/a556d8cf-b109-5b40-9af4-6555b827d0a6
-- title:
--   Aff Glue: sec Equiv res M
-- statement:
--   The Aff Glue construction uses the sec Equiv res M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SecEquivResM.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SecEquivResM.lean#L129-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecEquivResM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AffGlue
attribute [instance] Data.grp Data.mod
variable {T : Scheme.{0}} (D : Data T)
variable {D}

theorem GlobalTheory.AffGlue.secEquiv_resM (hD : (famPresheaf D).IsSheaf) {V V' : T.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (h : V' ≤ V) (s : Γ(toModules D hD, V)) :
    secEquiv hD hV' (GlobalTheory.Twist.resM (toModules D hD) h s) = D.ρ hV hV' h (secEquiv hD hV s) := by sorry
