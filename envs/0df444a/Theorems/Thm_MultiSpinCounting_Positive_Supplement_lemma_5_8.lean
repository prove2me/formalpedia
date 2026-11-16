-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_Supplement_lemma_5_8
-- name    : MultiSpinCounting.Positive.Supplement.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:28:06.95764+00:00
-- url     : https://prove2.me/theorems/c7cb6c1a-6d3f-4ede-af76-110cfccc8917
-- title:
--   Lemma 5.8 (used in the proof of Theorem 1.7) — weighted-path decay
-- statement:
--   Fix $0<\eta<1$, real $d\ge8$, and integer $q\ge(2+\eta)d$, with the explicit parameter estimates (5.13)–(5.15). Define $D,\gamma,\lambda_0,\rho$ as in (5.10), (5.12), and let $W_\ell(G)$ sum $\prod_{i=1}^{\ell}w(v_i)$ over ordered simple paths, where $w(v)=\gamma$ at degree at most $D$ and $w(v)=1$ otherwise. For every positive integer $n\ge\max\{d,2+12/\eta\}$,
--   $$\mathbb P_{G\sim G(n,d/n)}\!\left[\exists\,1\le\ell<n:\ W_\ell(G)>n^6\rho^\ell\right]\le n^{-4}.$$
--   The initial path vertex is excluded from the product. This gives simultaneous decay for all path lengths needed in the error bound.
--
--   Differences from the source:
--   - generalization: the standing assumption d ≥ d0(η) → d ≥ 8 and the explicit estimates (5.13)–(5.15); reason: Lemma B.1 supplies all these inequalities for the source regime; the proofs use only these consequences
--   - encoding: G(n,d/n) for n ≥ d → the published clamped Erdős–Rényi law; reason: the clamp is the identity throughout this lemma’s domain
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 24, Lemma 5.8

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Supplement_RandomGraphs

namespace MultiSpinCounting.Positive.Supplement

/-- Lemma 5.8, p. 24; section assumptions replaced by their explicit estimates. -/
theorem lemma_5_8 (η d : ℝ) (q : ℕ) (hη : 0 < η ∧ η < 1)
    (hd : 8 ≤ d) (hq : (2 + η) * d ≤ (q : ℝ))
    (hparams : ParameterEstimates η d q) (n : ℕ) (hn : 0 < n)
    (hsize : max d (2 + 12 / η) ≤ (n : ℝ)) :
    LPCommunity.SBMRecovery.erProb n (d / n)
      (fun G => ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ < n ∧
        (n : ℝ) ^ 6 * rho5 η ^ ℓ < pathWeight G d q ℓ) ≤
      (n : ℝ) ^ (-4 : ℤ) := by sorry

end MultiSpinCounting.Positive.Supplement
