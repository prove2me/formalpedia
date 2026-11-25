-- Prove2me | Theorems.Thm_GlobalTheory_GenusLatCompare_harmL_eq
-- name    : GlobalTheory.GenusLatCompare.harmL_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:21.912264+00:00
-- url     : https://prove2.me/theorems/156ca368-489d-4959-a446-e9f455040b27
-- title:
--   Genus Lat Compare: harm L eq
-- statement:
--   The Genus Lat Compare construction uses the harm L eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsMulMemOfMemSpan.lean#L228-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsMulMemOfMemSpan.lean#L228-L232

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNeZeroSmulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
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
open GlobalTheory GlobalTheory.GenusLatCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped Pointwise
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
variable [IsCMField E]
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

theorem GlobalTheory.GenusLatCompare.harmL_eq (Λ : Lat E n) (a : (E →+* ℂ) × ℕ → ℕ) :
    harmL (Dw := Dw) c (toGen Λ) a = harmLat Dw c a Λ := by sorry
