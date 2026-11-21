-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_phase_amplitude
-- name    : MomentSearch.rakhmanov_phase_amplitude
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:52:28.129475+00:00
-- url     : https://prove2.me/theorems/8c70806f-ee2d-4f55-9d85-e1ab167dbcef
-- title:
--   Phase and amplitude of Rakhmanov’s equilibrium polynomial
-- statement:
--   Let $1\le k<N$, put $r=\sqrt{1-(k/N)^2}$, and define the density on $[-1,1]$ by
--   $$
--   \rho(t)=\frac{N}{\pi}\arctan\!\left(\frac{N}{k}\sqrt{\max(0,r^2-t^2)}\right).
--   $$
--   Write $\phi(x)=\pi\int_x^1\rho(t)\,dt$ and $L(x)=\int_{-1}^1\rho(t)\log|x-t|\,dt$. There is a real polynomial $S$ of degree at most $N-k$ and a positive continuous amplitude $A$ on $[-1,1]$ such that
--   $$
--   S(x)=A(x)e^{L(x)}\cos\phi(x)
--   \quad\text{and}\quad A(z)\le 12 A(x)\qquad (x,z\in[-1,1]).
--   $$
--   This is the phase-amplitude estimate of Rakhmanov’s Lemma 2, with $L=-V_2$.
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Annals of Mathematics 165 (2007), p. 64, Lemma 2, equations (2.14)–(2.15), and §3.3, pp. 77–82. https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n1-p03.pdf

import Mathlib

theorem MomentSearch.rakhmanov_phase_amplitude (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun t => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - t ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let L : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, ρ t * Real.log |z - t|
    ∃ S : Polynomial ℝ, ∃ A : ℝ → ℝ,
      S.natDegree ≤ N - k ∧ ContinuousOn A (Set.Icc (-1 : ℝ) 1) ∧
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, 0 < A z ∧ S.eval z = A z * Real.exp (L z) * f z) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ z ∈ Set.Icc (-1 : ℝ) 1, A z ≤ 12 * A x) := by sorry
