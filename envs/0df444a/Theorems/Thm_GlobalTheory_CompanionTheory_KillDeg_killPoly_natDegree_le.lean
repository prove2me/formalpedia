-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KillDeg_killPoly_natDegree_le
-- name    : GlobalTheory.CompanionTheory.KillDeg.killPoly_natDegree_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:29.774808+00:00
-- url     : https://prove2.me/theorems/c894d6af-ac4e-55fd-b0e2-c8d84e3a3aa6
-- title:
--   Kill Deg: kill Poly nat Degree le
-- statement:
--   The Kill Deg construction uses the kill Poly nat Degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsRecurrencePolynomial.lean#L122-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsRecurrencePolynomial.lean#L122-L284

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsRecurrencePolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KillDeg

theorem GlobalTheory.CompanionTheory.KillDeg.killPoly_natDegree_le (G : Type) [Group G] (a : ℝ → G) (F₀ : G → ℂ)
    (S : Submodule ℂ (ℝ → ℂ)) (ha : ∀ s t, a (s + t) = a s * a t)
    (hcont : ∀ g, Continuous fun t => F₀ (a t * g)) (hfin : FiniteDimensional ℂ S)
    (hS : ∀ g, (fun t => F₀ (a t * g)) ∈ S) :
    ∃ p : ℂ[X], p.Monic ∧ p.natDegree ≤ Module.finrank ℂ S ∧
      (∀ g, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * F₀ (a j * g) = 0) ∧
      ∀ z, p.IsRoot z → ∃ c : ℂ, z = Complex.exp c ∧
        ∃ F ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => F₀ (a t * g)), F ≠ 0 ∧
          ∀ (t : ℝ) g, F (a t * g) = Complex.exp (c * t) * F g := by sorry
