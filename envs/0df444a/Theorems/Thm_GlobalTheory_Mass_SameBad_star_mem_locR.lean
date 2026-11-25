-- Prove2me | Theorems.Thm_GlobalTheory_Mass_SameBad_star_mem_locR
-- name    : GlobalTheory.Mass.SameBad.star_mem_locR
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:52:49.986359+00:00
-- url     : https://prove2.me/theorems/6cf0226e-0355-58bf-9281-cfd97d1e1602
-- title:
--   Same Bad: star mem loc R
-- statement:
--   The Same Bad construction uses the star mem loc R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DefiniteHermitianIsometricOfSameBadPrimes.lean#L41-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DefiniteHermitianIsometricOfSameBadPrimes.lean#L41-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteHermitianIsometricOfSameBadPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SameBad
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem GlobalTheory.Mass.SameBad.star_mem_locR {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : conjIdeal (K := K) P = P) {a : K}
    (ha : a ∈ locR (K := K) P) : star a ∈ locR (K := K) P := by sorry
