-- Prove2me | Theorems.Thm_GlobalTheory_ZMTFin_isFinite_toBase
-- name    : GlobalTheory.ZMTFin.isFinite_toBase
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:18.399805+00:00
-- url     : https://prove2.me/theorems/5a3405f7-6909-4fb1-849d-10b85352da5d
-- title:
--   ZMTFin: is Finite to Base
-- statement:
--   The ZMTFin construction uses the is Finite to Base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCompOpenImmersionOfQuasiFinite.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCompOpenImmersionOfQuasiFinite.lean#L91-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetAwayMapSubalgebraBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCoequifiberedSubalgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelSpecMapIsIsoOverBasicOpenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalizationBasicOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapBijectiveOfRangeEqSubalgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCompOpenImmersionOfQuasiFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
open GlobalTheory GlobalTheory.ZMTFin
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.ZMTFin.isFinite_toBase (X : Scheme.{0}) (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (h : α'.Coequifibered)
    (hfin : ∀ V, (α'.app V).hom.Finite) : IsFinite (relativeGluingData h).toBase := by sorry
