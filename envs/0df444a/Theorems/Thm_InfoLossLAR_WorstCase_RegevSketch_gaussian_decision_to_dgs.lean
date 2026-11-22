-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_gaussian_decision_to_dgs
-- name    : InfoLossLAR.WorstCase.RegevSketch.gaussian_decision_to_dgs
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:12:54.563742+00:00
-- url     : https://prove2.me/theorems/f4be78a2-8439-4d72-9621-5f6b7a9f0248
-- title:
--   Gaussian decision advantage yields a uniform joint DGS sampler
-- statement:
--   Let $D$ be a uniform quantum polynomial-time distinguisher, $t$ a positive polynomially bounded sample-count function, $b\in\mathbb N$, and $S$ an infinite set of positive parameters. Suppose the advantage of $D$ against the fixed public family's Gaussian block-LWE distribution is at least $n^{-b}$ for all sufficiently large $n\in S$.
--
--   There are one uniform multi-output quantum polynomial-time family $G$, one negligible function $\delta$, and a cutoff $n_0$ such that
--
--   $$
--   \forall n\in S,\ n\ge n_0\ \Longrightarrow\ \mathrm{DGSAt}(G,n,\delta(n)).
--   $$
--
--   The concrete DGS predicate concerns arbitrary nonsingular original integer bases, rational widths at or above the fixed smoothing threshold, and complete coefficient pools. The same sampler handles all unary pool sizes and unary numerical-error budgets, with total eventwise error $m\delta(n)+1/(u+1)$.
--
--   This is the open algorithmic core of the reduction. Its source route includes decision-to-search, verification and the noise grid, modular closest-vector recovery, BDD construction, wide-Gaussian initialization, pure-state preparation, the BDD-to-DGS quantum step, and width iteration. The statement does not assume any of these algorithms as an oracle. Neither $t$ nor $S$ is required to be computable.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Theorem 3.1; Lemmas 4.1–4.2, 3.5–3.7, 3.11 and 3.4, 3.2, 3.12 and Claim 3.13, 3.14, and 3.3. The discrete Gaussian block-input and uniform finite-gate contracts are the explicit fixed-family formalization of this route.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem gaussian_decision_to_dgs :
  ∀ D : Family,IsQPT D → ∀ t : ℕ → ℕ,(∀ n,1 ≤ t n) → PolyBoundedFn t →
    ∀ b : ℕ,∀ S : Set ℕ,S.Infinite → (∀ n ∈ S,1 ≤ n) →
      (∃ n₀ : ℕ,∀ n ∈ S,n₀ ≤ n → (n : ℝ)^(-(b : ℝ)) ≤
        advLWE D n (famPP n) (famq n) (famN n) (famd n) (t n)
          (chiG (famq n) (famd n) (famσ n))) →
      ∃ G : MFamily,IsMQPT G ∧ ∃ error : ℕ → ℝ,Negligible error ∧
        ∃ cutoff : ℕ,∀ n ∈ S,cutoff ≤ n → DGSAt G n (error n) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
