-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBetaCompare_span_image_ideal
-- name    : GlobalTheory.LatticeBetaCompare.span_image_ideal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:15.959917+00:00
-- url     : https://prove2.me/theorems/c5489ea8-a4d3-5457-8d81-17e32bdc3af6
-- title:
--   Lattice Beta Compare: span image ideal
-- statement:
--   The Lattice Beta Compare construction uses the span image ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L192-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L192-L197

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

theorem GlobalTheory.LatticeBetaCompare.span_image_ideal (𝔞 : Ideal (𝓞 E)) :
    Submodule.span (𝓞 F) (φ.comp (algebraMap (𝓞 E) E) '' (𝔞 : Set (𝓞 E))) =
      coeI F (𝔞.map (RingOfIntegers.mapRingHom φ)) := by sorry
