-- Prove2me | Theorems.Thm_GlobalTheory_absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified
-- name    : GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:13.8659+00:00
-- url     : https://prove2.me/theorems/50ca3e1c-0122-412e-9ba2-6ef74fa52862
-- title:
--   Global Theory: abs Norm prime iff inertia Deg eq one and finite ramified
-- statement:
--   The Global Theory construction uses the abs Norm prime iff inertia Deg eq one and finite ramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified.lean#L8-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified.lean#L8-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
open NumberField IsDedekindDomain

theorem GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified :
    ∀ (E : Type) [Field E] [NumberField E],
      (∀ P : HeightOneSpectrum (𝓞 E),
        (Ideal.absNorm P.asIdeal).Prime ↔ P.asIdeal.inertiaDeg ℤ = 1) ∧
      {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.ramificationIdx ℤ ≠ 1}.Finite := by sorry
