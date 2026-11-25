-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_finite_forall_liesOver
-- name    : GroundTheory.Global.exists_finite_forall_liesOver
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:44.073849+00:00
-- url     : https://prove2.me/theorems/1cb717f3-1d7c-4c34-a09b-6e7352ff0fba
-- title:
--   Global: exists finite forall lies Over
-- statement:
--   The Global construction uses the exists finite forall lies Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/BadPrimesFinite.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/BadPrimesFinite.lean#L18-L23

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_FunctionFieldIntegral
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_BadPrimesFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsLocalRing WeierstrassCurve.Affine
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.Global.exists_finite_forall_liesOver {p : HeightOneSpectrum (𝓞 L) → Prop}
    (hp : ∀ᶠ w in Filter.cofinite, p w) :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v ∉ T, ∀ w : HeightOneSpectrum (𝓞 L),
      w.asIdeal.LiesOver v.asIdeal → p w := by sorry
