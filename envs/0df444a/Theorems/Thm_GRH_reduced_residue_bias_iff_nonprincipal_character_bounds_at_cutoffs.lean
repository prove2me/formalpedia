-- Prove2me | Theorems.Thm_GRH_reduced_residue_bias_iff_nonprincipal_character_bounds_at_cutoffs
-- name    : GRH.reduced_residue_bias_iff_nonprincipal_character_bounds_at_cutoffs
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T13:04:28.311689+00:00
-- url     : https://prove2.me/theorems/08749648-06a2-45af-9c07-753b3a57e9d1
-- title:
--   Centered residue-class bounds are equivalent to bounds for the nonprincipal character sums
-- statement:
--   For any positive modulus $q$, real weights $w(k)$, integer cutoffs $n(u)$ and real comparison function $g(u)$, write $R_a(u)$ for the sum of the weights in the unit class $a$ through $n(u)$ and $P(u)$ for the sum over all unit classes. Every $|R_a(u)-P(u)/\varphi(q)|$ is bounded by $C_a g(u)$ with $C_a\ge0$ precisely when every nonprincipal character sum $|\sum_{k\le n(u)}\chi(k)w(k)|$ is bounded by $D_\chi g(u)$ with $D_\chi\ge0$. All cutoffs, including zero, are covered.
-- source:
--   Derived in the centered Möbius bilinear problem https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and the square-cutoff residue-bias reduction https://prove2.me/theorems/ebfcf6de-c11b-4420-bb99-92e3875c1325.

import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open scoped BigOperators

theorem GRH.reduced_residue_bias_iff_nonprincipal_character_bounds_at_cutoffs (q : ℕ) [NeZero q] (w : ℕ → ℝ) (n : ℕ → ℕ) (g : ℕ → ℝ) :
    (∀ a : ZMod q, IsUnit a → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (n u + 1), if (k : ZMod q) = a then w k else 0) -
        (∑ k ∈ Finset.range (n u + 1), if IsUnit (k : ZMod q) then w k else 0) /
          (q.totient : ℝ)| ≤ C * g u) ↔
    (∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      ‖∑ k ∈ Finset.range (n u + 1), χ k * (w k : ℂ)‖ ≤ D * g u) := by sorry
