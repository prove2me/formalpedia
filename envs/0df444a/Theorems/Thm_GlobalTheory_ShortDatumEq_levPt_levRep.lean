-- Prove2me | Theorems.Thm_GlobalTheory_ShortDatumEq_levPt_levRep
-- name    : GlobalTheory.ShortDatumEq.levPt_levRep
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:42.635925+00:00
-- url     : https://prove2.me/theorems/69aaa13d-277a-45be-85c4-4048abb403bf
-- title:
--   Short Datum Eq: lev Pt lev Rep
-- statement:
--   The Short Datum Eq construction uses the lev Pt lev Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdmissibleFalseIffFirstInvariant.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdmissibleFalseIffFirstInvariant.lean#L33-L35

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

theorem GlobalTheory.ShortDatumEq.levPt_levRep (Xo : Moduli D l) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) (q : LevQ D l) :
    levPt Xo x0 (levRep q) = levPtCl Xo x0 q := by sorry
