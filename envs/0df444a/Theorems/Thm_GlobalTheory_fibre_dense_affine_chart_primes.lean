-- Prove2me | Theorems.Thm_GlobalTheory_fibre_dense_affine_chart_primes
-- name    : GlobalTheory.fibre_dense_affine_chart_primes
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:29.513633+00:00
-- url     : https://prove2.me/theorems/c9693ab6-dd2e-4562-892d-51456193b593
-- title:
--   Global Theory: fibre dense affine chart primes
-- statement:
--   The Global Theory construction uses the fibre dense affine chart primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FibreDenseAffineChartPrimes.lean#L6-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FibreDenseAffineChartPrimes.lean#L6-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreDenseAffineChartPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Topology
open GlobalTheory

theorem GlobalTheory.fibre_dense_affine_chart_primes : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens) (U : X.Opens) (V : T.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : U ≤ p ⁻¹ᵁ V),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) →
    ∀ q : PrimeSpectrum Γ(X, U), q ∈ closure ({P : PrimeSpectrum Γ(X, U) | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (p.appLE V U e).hom ⁻¹' {PrimeSpectrum.comap (p.appLE V U e).hom q}) := by sorry
