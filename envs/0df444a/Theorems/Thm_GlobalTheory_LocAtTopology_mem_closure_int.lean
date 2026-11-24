-- Prove2me | Theorems.Thm_GlobalTheory_LocAtTopology_mem_closure_int
-- name    : GlobalTheory.LocAtTopology.mem_closure_int
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:13:26.050108+00:00
-- url     : https://prove2.me/theorems/7ef34d22-eb5d-4ca9-a11b-58c19743116b
-- title:
--   Loc At Topology: mem closure int
-- statement:
--   The Loc At Topology construction uses the mem closure int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceOfNonarchimedeanLocalField.lean#L41-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceOfNonarchimedeanLocalField.lean#L41-L81

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIntegersLocalisationIffSumCmDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LocAtTopology
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem GlobalTheory.LocAtTopology.mem_closure_int (T : LocAt F E sig p) (c : T.Fp) (hc : c ∈ 𝒪[T.Fp]) :
    c ∈ closure (Set.range fun a : 𝓞 F => T.ιF (algebraMap (𝓞 F) F a)) := by sorry
