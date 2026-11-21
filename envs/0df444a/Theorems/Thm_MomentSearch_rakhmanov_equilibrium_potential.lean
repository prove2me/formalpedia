-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_equilibrium_potential
-- name    : MomentSearch.rakhmanov_equilibrium_potential
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:52:27.355925+00:00
-- url     : https://prove2.me/theorems/b596f12e-ef56-488d-9468-bd4d593d84b5
-- title:
--   Equilibrium logarithmic potential for Rakhmanov’s density
-- statement:
--   Let $1\le k<N$ and $r=\sqrt{1-(k/N)^2}$. Define
--   $$
--   \rho(t)=\frac{N}{\pi}\arctan\!\left(\frac{N}{k}\sqrt{\max(0,r^2-t^2)}\right),
--   \qquad L(x)=\int_{-1}^1\rho(t)\log|x-t|\,dt.
--   $$
--   Write
--   $$
--   V(x)=\frac N2\big((1+x)\log(1+x)+(1-x)\log(1-x)\big),
--   $$
--   where the product $u\log u$ at $u=0$ has value zero. Then $L-V$ is constant on $[-r,r]$ and is at most that constant throughout $[-1,1]$. Here $L=-V_2$ and $V=N-V_1$ in Rakhmanov’s notation, so the conclusion is the equilibrium relation (2.17).
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Annals of Mathematics 165 (2007), p. 64, Lemma 3, equation (2.17), and §4.1, pp. 82–84. https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n1-p03.pdf

import Mathlib

theorem MomentSearch.rakhmanov_equilibrium_potential (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun t => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - t ^ 2))
    let L : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, ρ t * Real.log |z - t|
    let V : ℝ → ℝ := fun z => (N : ℝ) / 2 *
      ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z))
    ∃ K : ℝ,
      (∀ x ∈ Set.Icc (-r) r, L x - V x = K) ∧
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, L z - V z ≤ K) := by sorry
