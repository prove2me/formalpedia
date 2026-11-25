-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBetaCompare_smul_eq_coeI_mul
-- name    : GlobalTheory.LatticeBetaCompare.smul_eq_coeI_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:30:30.058171+00:00
-- url     : https://prove2.me/theorems/4cf931b3-b2cd-5e63-8415-23da61fa29f5
-- title:
--   Lattice Beta Compare: smul eq coe I mul
-- statement:
--   The Lattice Beta Compare construction uses the smul eq coe I mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L185-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L185-L190

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
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
open GlobalTheory GlobalTheory.LatticeBetaCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise
variable {E F : Type} [Field E] [Field F] (φ : E →+* F)

theorem GlobalTheory.LatticeBetaCompare.smul_eq_coeI_mul (𝔞 : Ideal (𝓞 E)) (N : Submodule (𝓞 E) E) : 𝔞 • N = coeI E 𝔞 * N := by sorry
