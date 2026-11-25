-- Prove2me | Theorems.Thm_GlobalTheory_GenusLatCompare_levOK_iff
-- name    : GlobalTheory.GenusLatCompare.levOK_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:03.435245+00:00
-- url     : https://prove2.me/theorems/4860dec3-971c-45cf-8c8f-f6dda108ff50
-- title:
--   Genus Lat Compare: lev OK iff
-- statement:
--   The Genus Lat Compare construction uses the lev OK iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsMulMemOfMemSpan.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsMulMemOfMemSpan.lean#L36-L37

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

theorem GlobalTheory.GenusLatCompare.levOK_iff (Λ : Lat E n) (N M : ℕ) : (toGen Λ).LevOK N M ↔ Λ.Admissible M N := by sorry
