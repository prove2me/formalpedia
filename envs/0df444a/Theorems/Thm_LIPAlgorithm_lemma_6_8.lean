-- Prove2me | Theorems.Thm_LIPAlgorithm_lemma_6_8
-- name    : LIPAlgorithm.lemma_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:56.685873+00:00
-- url     : https://prove2.me/theorems/7a4f6042-301b-45f3-9d48-8278e2d8c458
-- title:
--   Lemma 6.8 — a birthday collision sees the square-biased law
-- statement:
--   Let $L$ be a full-rank lattice of rank $n\ge1$, $s>0$, $\mu=D_{L^*,s}$ and $S_2(\mu)=(\sum_x\mu(x)^2)^{-1}$. Weighting $x$ proportionally to $\mu(x)^2$ gives exactly $D_{L^*,s/\sqrt2}$: for every $K\subseteq L^*$,
--
--   $$\sum_{x\in K}S_2(\mu)\mu(x)^2=\Pr_{X\sim D_{L^*,s/\sqrt2}}[X\in K].$$
--
--   This identifies the law that governs birthday collisions, which is why Corollary 4.7 is also needed at parameter $s/\sqrt2$.
--
--   Differences from the source:
--   - generalization: μ = D_{L*,s} in the setting of Lemma 6.7 (L well-rounded, s = Cn²log n/λ) → every lattice and every s > 0; reason: the lemma's proof is pointwise algebra; the source's case is an instance
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Lemma 6.8, p.34

import Mathlib
import Definitions.Def_LIPAlgorithm_heatDelta

namespace LIPAlgorithm

/-- **Lemma 6.8 (A birthday collision sees the square-biased law).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript
sha256 61ee52aa…), Lemma 6.8, p.34 (PDF p.37). With `μ = D_{L*,s}` and `S₂(μ) = (∑ₓ μ(x)²)⁻¹`: for every `K ⊆ L*`,
`∑_{x ∈ K} S₂(μ)·μ(x)² = Pr_{X ∼ D_{L*,s/√2}}[X ∈ K]`. -/
theorem lemma_6_8 (n : ℕ) (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L] (s : ℝ)
    (hn : 1 ≤ n) (hs : 0 < s) (K : Set (RegevLWE.GaussConv.dual L)) :
    ∑' x : RegevLWE.GaussConv.dual L,
        K.indicator (fun x => collisionScale L s *
          RegevLWE.Hyperplane.discreteGaussian (RegevLWE.GaussConv.dual L) s x ^ 2) x =
      gaussProb L (s / Real.sqrt 2) K := by sorry

end LIPAlgorithm
