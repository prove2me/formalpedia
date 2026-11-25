-- Prove2me | Theorems.Thm_GroundTheory_Global_multiplicity_differentIdeal_eq_differentExponent
-- name    : GroundTheory.Global.multiplicity_differentIdeal_eq_differentExponent
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:54:10.345622+00:00
-- url     : https://prove2.me/theorems/03704db8-42a5-52cb-ae6f-4e698433dfeb
-- title:
--   Global: multiplicity different Ideal eq different Exponent
-- statement:
--   The Global construction uses the multiplicity different Ideal eq different Exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L325-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L325-L336

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem GroundTheory.Global.multiplicity_differentIdeal_eq_differentExponent (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
    [iA : Algebra (v.adicCompletion K) (w.adicCompletion M)]
    [ContinuousSMul (v.adicCompletion K) (w.adicCompletion M)]
    [IsScalarTower K (v.adicCompletion K) (w.adicCompletion M)] :
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 M)) =
      differentExponent (v.adicCompletion K) (w.adicCompletion M) := by sorry
