-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_search_to_dgs
-- name    : InfoLossLAR.WorstCase.RegevSearch.search_to_dgs
-- status  : Open
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:12:01.859192+00:00
-- url     : https://prove2.me/theorems/7b4400cb-1d0c-4066-9f5f-a61d09f19b20
-- title:
--   Fixed-family Gaussian LWE search to joint lattice Gaussian sampling
-- statement:
--   Let $S$ be an infinite set of positive security parameters. Suppose one uniform quantum polynomial-time algorithm recovers every secret with probability at least $3/4$ from fresh fixed-family Gaussian LWE tables, using one fixed polynomial number of blocks, at every sufficiently large parameter in $S$. Then there is one uniform quantum polynomial-time sampler $G$ and one negligible function $\varepsilon$ such that, for every sufficiently large $n\in S$, $G$ satisfies the joint-output lattice Gaussian sampling contract $\operatorname{DGSAt}(G,n,\varepsilon(n))$.
--
--   For every nonsingular integer basis and every positive rational width at least the contract threshold, this contract bounds the discrepancy of every event on the *whole decoded coefficient pool* by
--
--   $$
--   \text{count}\cdot\varepsilon(n)+\frac{1}{\text{budget}+1}.
--   $$
--
--   The input explicitly includes the output count and numerical budget in unary. The obligation includes arbitrary basis encodings, the joint output law, and a negligible term independent of the basis and requested budget. It is not a claim that the searcher works on smaller-noise inputs, that repeated calls using a shared pool are independent, or that the sampler is already constructed.
--
--   **Formalization Note.** This is a fixed-family, discrete-noise and uniform-circuit formulation inspired by Regev's continuous-noise reduction. The noise conversion, success amplification, coherent BDD use, numerical errors, iteration, and full joint-law strengthening remain part of this open theorem rather than being assumed as already proved by the source.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Theorem 3.1 and Lemmas 3.2–3.7, 3.11 and 3.14, pp. 18–28; Chen Qian, arXiv:2611.05136, Appendix I.1, pp. 132–133. The precise discrete Gaussian, fixed-family encodings, uniform circuit, numeric and joint-output conditions are explicit formalization obligations and are not a verbatim claim of either source.

import Definitions.Def_InfoLossLAR_RegevSearch

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open InfoLossLAR.WorstCase.RegevSketch InfoLossLAR.WorstCase.RegevSearch

namespace InfoLossLAR.WorstCase.RegevSearch
theorem search_to_dgs : ∀ (S : Set ℕ), S.Infinite → (∀ n ∈ S, 1 ≤ n) →
      ∀ (A : MFamily), IsMQPT A → ∀ (samples : Polynomial ℕ) (cutoff : ℕ),
        SearchOn A samples cutoff S →
        ∃ G : MFamily, IsMQPT G ∧ ∃ error : ℕ → ℝ, InfoLossLAR.WorstCase.Negligible error ∧
          ∃ threshold : ℕ, ∀ n ∈ S, threshold ≤ n → DGSAt G n (error n) := by sorry
end InfoLossLAR.WorstCase.RegevSearch
