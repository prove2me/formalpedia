-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_equilibrium_potential_comparison
-- name    : MomentSearch.rakhmanov_equilibrium_potential_comparison
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:52:47.023383+00:00
-- url     : https://prove2.me/theorems/f31fa178-b3a8-4b5a-833f-569bb95ea266
-- title:
--   Equilibrium potential comparison on the central interval
-- statement:
--   For the equilibrium density $\rho$, write $V(z)=\int_{-1}^1\log(1/|z-t|)\rho(t)\,dt$ and $w(z)=\exp(-N[(1+z)\log(1+z)+(1-z)\log(1-z)]/2)$. There is a real constant $d$ with
--   $$V(x)-\log w(x)=d\quad(|x|<r),\qquad V(z)-\log w(z)\ge d\quad(|z|\le1).$$
--   The normalization of the uniform-grid potential is absorbed into $d$.
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Lemma 3, (2.17), §4, https://annals.math.princeton.edu/2007/165-1/p03

import Mathlib

theorem MomentSearch.rakhmanov_equilibrium_potential_comparison (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let w : ℝ → ℝ := fun z => Real.exp (-(N : ℝ) / 2 *
      ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)))
    let V : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, Real.log (1 / |z-t|) * ρ t
    ∃ d : ℝ,
      (∀ x ∈ Set.Ioo (-r) r, V x - Real.log (w x) = d) ∧
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, d ≤ V z - Real.log (w z) := by sorry
