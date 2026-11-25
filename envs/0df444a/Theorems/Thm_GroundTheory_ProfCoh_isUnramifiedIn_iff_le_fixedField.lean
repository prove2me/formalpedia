-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedIn_iff_le_fixedField
-- name    : GroundTheory.ProfCoh.isUnramifiedIn_iff_le_fixedField
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:45.464129+00:00
-- url     : https://prove2.me/theorems/a29ddee0-92db-4fe8-98ab-15b1bc09e25f
-- title:
--   Prof Coh: is Unramified In iff le fixed Field
-- statement:
--   The Prof Coh construction uses the is Unramified In iff le fixed Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L72-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L72-L84

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
open scoped Pointwise
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem GroundTheory.ProfCoh.isUnramifiedIn_iff_le_fixedField {E M : IntermediateField F Ω} (h : E ≤ M)
    [FiniteDimensional F M] [IsGalois F M] (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal ↔
      ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.LiesOver v.asIdeal →
        E ≤ (IntermediateField.fixedField (Q.inertia Gal(M/F))).map M.val := by sorry
