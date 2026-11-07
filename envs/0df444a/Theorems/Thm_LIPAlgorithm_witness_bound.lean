-- Prove2me | Theorems.Thm_LIPAlgorithm_witness_bound
-- name    : LIPAlgorithm.witness_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:37.824782+00:00
-- url     : https://prove2.me/theorems/f3cd606b-c6e3-47ab-b624-64413cbf4366
-- title:
--   Proof of Theorem 6.9, (6.1)–(6.3) — a fixed isomorphism has a resolving witness
-- statement:
--   There is an absolute constant $c>0$ such that, for all $a\ge0$,
--
--   $$2e^{-a}-e^{-2a}\le\exp(-c\min\{a,a^2\}),$$
--
--   and the following holds for every full-rank lattice $L$ of rank $n\ge1$ and every $s>0$. With $\mu=D_{L^*,s}$ and $S=S_2(\mu)$: if $M\subseteq L^*$ has mass at least $0.99$ under $D_{L^*,s/\sqrt2}$, $T\ge1$ and $N\ge T\sqrt S$, then
--
--   $$\prod_{w\in M}\big(2e^{-N\mu(w)}-e^{-2N\mu(w)}\big)\le\exp(-cT).$$
--
--   In the Poissonized birthday sampling, this product is the probability (6.1) that a fixed isomorphism has no resolving witness, with $M$ the set of resolving markers. The bound permits a union bound over all isomorphisms.
--
--   Differences from the source:
--   - generalization: L well-rounded, s = Cn²log n/λ, and M the set of resolving markers → every lattice, every s > 0, and every M of mass at least 0.99; reason: these steps use only the mass (6.3); the source's case is an instance
--   - encoding: T = C₁κ/2, a_w = Np_w ≥ T√q_w, with N = ⌈C₁κ√Ŝ⌉ → any T ≥ 1 and N ≥ T√S; reason: N ≥ T√S gives a_w ≥ T√q_w; the printed values, with Ŝ = (1 ± o(1))S, are of this form
--   - encoding: the bound exp(−c∑_{w∈M}min{T√q_w, T²q_w}) ≤ exp(−cT∑q_w) ≤ exp(−Ω(C₁κ)) → exp(−c·T) with one absolute c; reason: (6.3) makes ∑q_w ≥ 0.99, which the constant absorbs
--   - encoding: the probability of no resolving witness equals (6.1) → the product (6.1) alone; reason: the Poissonization and independence steps are about the algorithm; they are carried by theorem_7_1
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Proof of Theorem 6.9, (6.1)–(6.3), pp.35–36

import Mathlib
import Definitions.Def_LIPAlgorithm_heatDelta

namespace LIPAlgorithm

/-- **The witness bound in the proof of Theorem 6.9.** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript sha256
61ee52aa…), proof of Theorem 6.9, (6.1)–(6.3), pp.35–36 (PDF pp.38–39).

With an absolute `c > 0`: the inequality (6.2), and the bound on the product (6.1): for `μ = D_{L*,s}`, `S₂ = S₂(μ)`, if `M ⊆ L*` has mass at
least `0.99` under `D_{L*,s/√2}` (this is (6.3)), `T ≥ 1` and `N ≥ T·√S₂`, then
`∏_{w ∈ M}(2e^{−Nμ(w)} − e^{−2Nμ(w)}) ≤ exp(−c·T)`.

**Formalization Note.** Each factor lies in `(0, 1]`, and `∑_w (1 − factor) ≤ N²·∑_w μ(w)² < ∞`, so the infinite product converges and
`∏'` has no default value. The printed `T = C₁κ/2` and `a_w ≥ T√q_w` are the case `N ≥ T√S₂`. The Poissonized no-witness
probability that equals (6.1) is carried by `theorem_7_1`. -/
theorem witness_bound :
    ∃ c : ℝ, 0 < c ∧
      (∀ a : ℝ, 0 ≤ a →
        2 * Real.exp (-a) - Real.exp (-(2 * a)) ≤ Real.exp (-(c * min a (a ^ 2)))) ∧
      ∀ (n : ℕ) (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L] (s : ℝ), 1 ≤ n → 0 < s →
        ∀ (M : Set (RegevLWE.GaussConv.dual L)) (T N : ℝ),
          (99 / 100 : ℝ) ≤ gaussProb L (s / Real.sqrt 2) M → 1 ≤ T →
          T * Real.sqrt (collisionScale L s) ≤ N →
            ∏' w : M,
              (2 * Real.exp (-(N * RegevLWE.Hyperplane.discreteGaussian (RegevLWE.GaussConv.dual L) s w)) -
                Real.exp (-(2 * (N * RegevLWE.Hyperplane.discreteGaussian (RegevLWE.GaussConv.dual L) s w)))) ≤
              Real.exp (-(c * T)) := by sorry

end LIPAlgorithm
