-- Prove2me | Theorems.Thm_GlobalTheory_GenusLatCompare_span_smul_le_iff
-- name    : GlobalTheory.GenusLatCompare.span_smul_le_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:59:33.645042+00:00
-- url     : https://prove2.me/theorems/62bbde47-cff2-465d-a8b0-5a7b7f067627
-- title:
--   Genus Lat Compare: span smul le iff
-- statement:
--   The Genus Lat Compare construction uses the span smul le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsMulMemOfMemSpan.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsMulMemOfMemSpan.lean#L46-L56

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
omit [NumberField E]

theorem GlobalTheory.GenusLatCompare.span_smul_le_iff (k : ℕ) (A B : Submodule (𝓞 E) (Fin n → E)) :
    Ideal.span {(k : 𝓞 E)} • A ≤ B ↔ ∀ x ∈ A, k • x ∈ B := by sorry
