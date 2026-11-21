-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_to_sivp
-- name    : InfoLossLAR.WorstCase.RegevSketch.dgs_to_sivp
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:13:43.641337+00:00
-- url     : https://prove2.me/theorems/7452f95c-25d4-4b6f-be9c-03c47887237e
-- title:
--   Uniform SIVP from a concrete joint DGS sampler
-- statement:
--   There are absolute natural numbers $C,k$, with $C\ge1$, with the following property. For every uniform multi-output quantum polynomial-time family $G$ and every negligible function $\delta$, there are a uniform multi-output quantum polynomial-time algorithm $A$ and a cutoff such that, at every positive dimension $n$ beyond the cutoff,
--
--   $$
--   \mathrm{DGSAt}(G,n,\delta(n))
--   \ \Longrightarrow\
--   A\text{ solves }\mathrm{SIVP}_{Cq(n)(\log_2(n+2))^k}.
--   $$
--
--   Success is required on every nonsingular integer-basis input, with the original platform vector encoding and success probability. The constants are fixed before the sampler and its error function; the algorithm and cutoff may depend on them.
--
--   The statement isolates the SIVP branch, including actual scale search and candidate selection. It does not assume that a satisfying DGS sampler exists.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Lemmas 3.15–3.17, full-version PDF pp. 28–29; fixed-family substitution and explicit uniform multi-output realization.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem dgs_to_sivp :
  ∃ C k : ℕ,1 ≤ C ∧ ∀ G : MFamily,IsMQPT G →
    ∀ error : ℕ → ℝ,Negligible error →
      ∃ A : MFamily,IsMQPT A ∧ ∃ cutoff : ℕ,∀ n ≥ cutoff,1 ≤ n →
        DGSAt G n (error n) →
          SolvesSIVP A (famN n) ((C : ℝ)*(famq n : ℝ)*Real.logb 2 ((n : ℝ)+2)^k) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
