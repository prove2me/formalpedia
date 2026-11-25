-- Prove2me | Theorems.Thm_GlobalTheory_GenusLatCompare_zCard_eq
-- name    : GlobalTheory.GenusLatCompare.zCard_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:07:12.940356+00:00
-- url     : https://prove2.me/theorems/ed69f0c9-6bf4-5b8f-9fdb-98c9536e917b
-- title:
--   Genus Lat Compare: z Card eq
-- statement:
--   The Genus Lat Compare construction uses the z Card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsMulMemOfMemSpan.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsMulMemOfMemSpan.lean#L42-L43

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

theorem GlobalTheory.GenusLatCompare.zCard_eq (Λ : Lat E n) (N r : ℕ) : (toGen Λ).zCard N r = Λ.cardZ r N := by sorry
