-- Prove2me | Theorems.Thm_GlobalTheory_HenselZero_fromSpecStalk_mem_basicOpen
-- name    : GlobalTheory.HenselZero.fromSpecStalk_mem_basicOpen
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:27.984123+00:00
-- url     : https://prove2.me/theorems/b275d0d5-4d6b-4a8e-8a46-c94369b83ca8
-- title:
--   Hensel Zero: from Spec Stalk mem basic Open
-- statement:
--   The Hensel Zero construction uses the from Spec Stalk mem basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsSectionOfTransversal.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsSectionOfTransversal.lean#L33-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSectionOfTransversal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.HenselZero

theorem GlobalTheory.HenselZero.fromSpecStalk_mem_basicOpen {X : Scheme.{0}} {y : X} {U : X.Opens} (hy : y ∈ U) (f : Γ(X, U))
    (q : Spec (X.presheaf.stalk y)) (hq : (X.presheaf.germ U y hy).hom f ∉ q.asIdeal) :
    X.fromSpecStalk y q ∈ X.basicOpen f := by sorry
