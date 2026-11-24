-- Prove2me | Theorems.Thm_GlobalTheory_GenusLatCompare_eqAtPrime_of_trivAt
-- name    : GlobalTheory.GenusLatCompare.eqAtPrime_of_trivAt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:59:34.938794+00:00
-- url     : https://prove2.me/theorems/7366cb06-970c-40ca-bebe-f58ffdcf7aed
-- title:
--   Genus Lat Compare: eq At Prime of triv At
-- statement:
--   The Genus Lat Compare construction uses the eq At Prime of triv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsMulMemOfMemSpan.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsMulMemOfMemSpan.lean#L77-L82

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

theorem GlobalTheory.GenusLatCompare.eqAtPrime_of_trivAt (Λ : GenLat E n) {s : ℕ} (h : Λ.TrivAt s) (p : ℕ) (hp : p.Prime) (hs : p ∣ s) :
    EqAtPrime p Λ.La (stdMod E n) := by sorry
