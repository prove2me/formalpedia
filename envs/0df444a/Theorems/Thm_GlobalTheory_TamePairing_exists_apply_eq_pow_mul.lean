-- Prove2me | Theorems.Thm_GlobalTheory_TamePairing_exists_apply_eq_pow_mul
-- name    : GlobalTheory.TamePairing.exists_apply_eq_pow_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:22.158812+00:00
-- url     : https://prove2.me/theorems/a3c7d510-6962-4554-8a65-ac7421f4f6a7
-- title:
--   Tame Pairing: exists apply eq pow mul
-- statement:
--   The Tame Pairing construction uses the exists apply eq pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TamePairing.lean#L71-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TamePairing.lean#L71-L82

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TamePairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.TamePairing
open GlobalTheory.TameQuot
open NumberField IsDedekindDomain
open scoped Pointwise

theorem GlobalTheory.TamePairing.exists_apply_eq_pow_mul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {v : HeightOneSpectrum (𝓞 F)} {N : ℕ} [NeZero N] {ζ x : Ω} (hζ : IsPrimitiveRoot ζ N)
    (hx : _root_.GlobalTheory.TameQuot.IsUnifRoot v N x) (g : _root_.Formalism.ConjugateSelfDual.G F Ω) : ∃ c : ZMod N, g x = ζ ^ c.val * x := by sorry
