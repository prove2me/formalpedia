-- Prove2me | Theorems.Thm_MarkovMixing_ising_block_dynamics
-- name    : MarkovMixing.ising_block_dynamics
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:27:44.765555+00:00
-- url     : https://prove2.me/theorems/e9ce639c-a4a0-49c6-af1d-9ddbec9ee83b
-- title:
--   Block dynamics comparison
-- statement:
--   Let $G$ be a graph with maximum degree $\Delta$ on a finite vertex set $V$, and let $\pi$ be the **Ising distribution** at inverse temperature $\beta>0$: $\pi(\sigma)\propto\exp\bigl(\beta\sum_{\{v,w\}\in E}\sigma(v)\sigma(w)\bigr)$ on spin configurations $\sigma:V\to\{\pm1\}$. Fix blocks $V_1,\dots,V_b\subseteq V$ covering $V$, each of size at most $M$, with every vertex lying in at most $M_\star$ blocks. The **block dynamics** picks a uniform block and re-samples the configuration on it from $\pi$ conditioned on the configuration outside; the **single-site Glauber dynamics** is the special case of singleton blocks. For either chain, the **spectral gap** is $\gamma=1-\lambda_2$ with $\lambda_2$ the largest eigenvalue different from $1$ (eigenvalues in the real-eigenvector sense of Mission VII); write $\gamma_B$ for the block dynamics' gap and $\gamma$ for the single-site gap.
--
--   The theorem (Theorem 15.9 of Levin–Peres–Wilmer) asserts the comparison
--   $$\gamma_B\;\le\;M^2\,M_\star\,\bigl(4\,e^{2\beta\Delta}\bigr)^{M+1}\;\gamma.$$
--
--   A spectral gap for the (coarse, easy-to-analyze) block dynamics transfers to the single-site dynamics at a cost depending only on the block size, the overlap multiplicity, the degree, and the temperature — not on the number of vertices. This is the engine of divide-and-conquer gap proofs: the book uses it for the tree theorem of this mission, and it is the template for gap bounds on lattices via recursive block decompositions. The proof routes each block update through a canonical path of single-site updates and bounds the congestion via the comparison method of Mission VII.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 15.5, Theorem 15.9, p. 209

import Definitions.Def_mm_ising

namespace MarkovMixing

/-- **Theorem 15.9** (LPW): comparison of the block dynamics and the
single-site Glauber dynamics for the Ising model: if the blocks cover the
vertex set, have size at most `M`, and each vertex lies in at most `M⋆`
blocks, then `γ_B ≤ M² M⋆ (4 e^{2βΔ})^{M+1} γ`. -/
theorem ising_block_dynamics {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    [Nonempty Vv] (G : SimpleGraph Vv) [DecidableRel G.Adj]
    (β : ℝ) (hβ : 0 < β) {b : ℕ} (hb : 0 < b) (blocks : Fin b → Finset Vv)
    (hcover : ∀ v : Vv, ∃ i : Fin b, v ∈ blocks i)
    (M Ms : ℕ) (hM : ∀ i : Fin b, (blocks i).card ≤ M)
    (hMs : ∀ v : Vv, (Finset.univ.filter fun i : Fin b => v ∈ blocks i).card ≤ Ms) :
    spectralGap (blockDynamics (isingDist G β) blocks) ≤
      (M : ℝ) ^ 2 * (Ms : ℝ) *
        (4 * Real.exp (2 * β * (G.maxDegree : ℝ))) ^ (M + 1) *
      spectralGap (glauber (isingDist G β)) := by
  sorry

end MarkovMixing
