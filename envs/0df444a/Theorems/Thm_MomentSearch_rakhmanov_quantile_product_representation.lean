-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_quantile_product_representation
-- name    : MomentSearch.rakhmanov_quantile_product_representation
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:52:45.74418+00:00
-- url     : https://prove2.me/theorems/1f667405-fc9e-4053-acc4-1127dc442763
-- title:
--   Cosine representation for the equilibrium quantile product
-- statement:
--   For the Rakhmanov equilibrium density $\rho$, let $V(z)=\int_{-1}^1\log(1/|z-t|)\rho(t)\,dt$ and $f(z)=\cos(\pi\int_z^1\rho(t)\,dt)$. There is a polynomial $S$ of degree at most $N-k$ and a positive continuous function $C$ on $[-1,1]$ such that
--   $$S(z)=C(z)e^{-V(z)}f(z),\qquad C(u)\le12C(v)\quad(-1\le u,v\le1).$$
--   In the quantile construction $S$ is the monic polynomial with roots at the half-integer mass levels.
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Lemma 2, (2.14)–(2.15), §3, https://annals.math.princeton.edu/2007/165-1/p03

import Mathlib

theorem MomentSearch.rakhmanov_quantile_product_representation (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let V : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, Real.log (1 / |z-t|) * ρ t
    ∃ S : Polynomial ℝ, ∃ C : ℝ → ℝ, S.natDegree ≤ N-k ∧
      ContinuousOn C (Set.Icc (-1 : ℝ) 1) ∧
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, 0 < C z ∧
        S.eval z = C z * Real.exp (-V z) * f z) ∧
      ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1, C u ≤ 12 * C v := by sorry
