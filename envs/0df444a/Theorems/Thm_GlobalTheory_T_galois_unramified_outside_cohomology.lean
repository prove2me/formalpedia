-- Prove2me | Theorems.Thm_GlobalTheory_T_galois_unramified_outside_cohomology
-- name    : GlobalTheory.T.galois_unramified_outside_cohomology
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:42.548155+00:00
-- url     : https://prove2.me/theorems/f42cfa79-2325-4edf-a519-596918431d0e
-- title:
--   T: galois unramified outside cohomology
-- statement:
--   The T construction uses the galois unramified outside cohomology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GaloisUnramifiedOutsideCohomologyStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GaloisUnramifiedOutsideCohomologyStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GaloisUnramifiedOutsideCohomology
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GaloisUnramifiedOutsideCohomologyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.galois_unramified_outside_cohomology : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), (maxUnramifiedOutside F Ω S).fixingSubgroup ≤ NS Ω S := by sorry
