-- Prove2me | Theorems.Thm_GlobalTheory_ShortDatumEq_datum_neg_eq_inv
-- name    : GlobalTheory.ShortDatumEq.datum_neg_eq_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:49.518619+00:00
-- url     : https://prove2.me/theorems/c08a20db-0d92-4424-9370-ddaa52d6d039
-- title:
--   Short Datum Eq: datum neg eq inv
-- statement:
--   The Short Datum Eq construction uses the datum neg eq inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdmissibleFalseIffFirstInvariant.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdmissibleFalseIffFirstInvariant.lean#L74-L78

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdmissibleFalseIffFirstInvariant
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
open GlobalTheory GlobalTheory.ShortDatumEq
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem GlobalTheory.ShortDatumEq.datum_neg_eq_inv (c : Coeff l) {n : ℕ} (x0 : Fin n → D.La) (q : Fin n → LevQ D l) :
    x0Dat c (-x0) q = (x0Dat c x0 q)⁻¹ := by sorry
