-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_recursion_mass
-- name    : KSATSingleFlip.Connect.soft_field_recursion_mass
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:24:20.439207+00:00
-- url     : https://prove2.me/theorems/0e56f0e2-1c23-45b6-9fb4-bb28157b2aa0
-- title:
--   Poisson soft-field update has the stated total mass
-- statement:
--   For a finite soft-field measure whose w-weighted intensity is finite and β ≥ 0, the kernel Kν is a probability measure and the total mass of Rβν equals β exp(h(ν)). This proves the mass recursion used in Lemma 4.5 under its finite-intensity condition.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and proof of Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open MeasureTheory ProbabilityTheory KSATSingleFlip.Connect
open scoped ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_recursion_mass (ν : Measure ℝ) [IsFiniteMeasure ν] (β : ℝ) (hβ : 0 ≤ β)
    (hfin : (ν.withDensity fun z => ENNReal.ofReal (wInt z)) Set.univ ≠ ∞) :
    Kmeas ν Set.univ = 1 ∧ (massM (Rbeta β ν)).toReal = β * Real.exp (hPot ν) := by sorry
