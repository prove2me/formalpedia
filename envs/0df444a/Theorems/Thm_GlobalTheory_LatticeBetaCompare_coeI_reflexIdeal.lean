-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBetaCompare_coeI_reflexIdeal
-- name    : GlobalTheory.LatticeBetaCompare.coeI_reflexIdeal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:49:38.58897+00:00
-- url     : https://prove2.me/theorems/92fac60b-90ad-5493-b8c0-01e618560484
-- title:
--   Lattice Beta Compare: coe I reflex Ideal
-- statement:
--   The Lattice Beta Compare construction uses the coe I reflex Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L229-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L229-L231

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

theorem GlobalTheory.LatticeBetaCompare.coeI_reflexIdeal (𝔞 : Ideal (𝓞 E)) : coeI c.F (reflexIdeal Dw c 𝔞) =
    ∏ τ : E →+* ℂ, coeI c.F (𝔞.map (RingOfIntegers.mapRingHom (embF c τ))) ^ Dw.mult τ := by sorry
