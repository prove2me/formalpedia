-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_finite_range_of_frob_pow_eq_one
-- name    : GlobalTheory.WeilDeligne.finite_range_of_frob_pow_eq_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:56.599236+00:00
-- url     : https://prove2.me/theorems/268b05f6-d0bb-40c6-af6e-327252148b9a
-- title:
--   Weil Deligne: finite range of frob pow eq one
-- statement:
--   The Weil Deligne construction uses the finite range of frob pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilDeligneInductionPrinciple.lean#L40-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilDeligneInductionPrinciple.lean#L40-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilDeligneInductionPrinciple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem GlobalTheory.WeilDeligne.finite_range_of_frob_pow_eq_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) {m : ℕ} (hm : 0 < m)
    (h1 : ρ (frob h) ^ m = 1) : (Set.range ρ).Finite := by sorry
