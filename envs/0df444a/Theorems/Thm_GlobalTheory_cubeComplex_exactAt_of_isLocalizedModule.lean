-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_exactAt_of_isLocalizedModule
-- name    : GlobalTheory.cubeComplex_exactAt_of_isLocalizedModule
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:15:05.549801+00:00
-- url     : https://prove2.me/theorems/209aa752-91e5-4ad4-8133-21b901d5bca1
-- title:
--   Global Theory: cube Complex exact At of is Localized Module
-- statement:
--   The Global Theory construction uses the cube Complex exact At of is Localized Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexExactAtOfIsLocalizedModuleRes.lean#L215-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexExactAtOfIsLocalizedModuleRes.lean#L215-L222

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v u
open GlobalTheory
variable {ι : Type} {R : Type u} [CommRing R]

theorem GlobalTheory.cubeComplex_exactAt_of_isLocalizedModule [LinearOrder ι] [Finite ι]
    (A : Cube.{v} ι R) (f : ι → R)
    {M : Type*} [AddCommGroup M] [Module R M] (g : ∀ s, M →ₗ[R] A.obj s)
    (hg : ∀ s, IsLocalizedModule.Away (∏ i ∈ s, f i) (g s))
    (hres : ∀ {s t : Finset ι} (h : s ⊆ t) (m : M), Cube.res A h (g s m) = g t m)
    (hf : Ideal.span (Set.range f) = ⊤) (p : ℕ) : (cubeComplex A).ExactAt p := by sorry
