-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBetaCompare_span_eq_coeI_iff
-- name    : GlobalTheory.LatticeBetaCompare.span_eq_coeI_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:21.789213+00:00
-- url     : https://prove2.me/theorems/043bafc5-c595-5809-8bf9-62e2ac51c1dc
-- title:
--   Lattice Beta Compare: span eq coe I iff
-- statement:
--   The Lattice Beta Compare construction uses the span eq coe I iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L206-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L206-L215

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

theorem GlobalTheory.LatticeBetaCompare.span_eq_coeI_iff [NumberField F] (β : F) (I : Ideal (𝓞 F)) :
    Submodule.span (𝓞 F) {β} = coeI F I ↔ ∃ b : 𝓞 F, (b : F) = β ∧ Ideal.span {b} = I := by sorry
