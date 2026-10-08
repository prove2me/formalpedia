-- Prove2me | Theorems.Thm_ModPolicyIter_Conv_lemma_1
-- name    : ModPolicyIter.Conv.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:13:52.047971+00:00
-- url     : https://prove2.me/theorems/38a6bf85-f5ed-47a1-a62a-d45bfd894e82
-- title:
--   Lemma 1, p. 1129 — U^k is a contraction with constant λ^{k+1}
-- statement:
--   Let $S$ be a set of states with a $\sigma$-algebra. Each policy $P\in\mathcal P$ is a Markov transition kernel on $S$ with a measurable one-period reward $c_P$, where $\sup_P\sup_s|c_P(s)|\le M$ and $0\le\lambda<1$. Let $V$ be the space of bounded measurable functions with $\|v\|=\sup_s|v(s)|$.
--
--   For $k\ge 0$ let $U^kv=\max_P\{\sum_{i=0}^k(\lambda P)^ic_P+(\lambda P)^{k+1}v\}$. Then for all $u,w\in V$
--
--   $$\|U^ku-U^kw\|\le\lambda^{k+1}\|u-w\|.$$
--
--   That is, $U^k$ is a contraction with modulus $\lambda^{k+1}$; for $k=0$ this is the classical contraction property of the value-iteration operator.
--
--   **Formalization Note** The conclusion includes both that $U^k$ maps $V$ into $V$ and the Lipschitz inequality. Since the pointwise supremum defining $U^k$ need not be measurable for an arbitrary policy family, the mapping property is an explicit hypothesis, as it is for Lemma 2 and Corollary 1. The paper treats it as implicit in calling $U^k$ an operator on $V$. The standing attainment assumption for $B$ is not needed for this contraction estimate.
-- source:
--   Puterman and Shin, Modified policy iteration algorithms for discounted Markov decision problems, Management Science 24 (1978), DOI 10.1287/mnsc.24.11.1127, p. 1129, Lemma 1

import Mathlib
import Definitions.Def_ModPolicyIter_Conv_Setting

open MeasureTheory ProbabilityTheory

namespace ModPolicyIter.Conv

/-- Lemma 1 (Puterman–Shin 1978, p. 1129): `U^k` is a contraction mapping of `V` with
constant `λ^{k+1}`. The explicit `hUV` supplies the paper's implicit assertion that the
pointwise maximum defining `U^k` is measurable and therefore maps `V` into `V`. -/
theorem lemma_1 {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι) (k : ℕ)
    (hUV : ∀ w : S → ℝ, IsBM w → IsBM (U m k w)) :
    (∀ w : S → ℝ, IsBM w → IsBM (U m k w)) ∧
      ∀ u w : S → ℝ, IsBM u → IsBM w →
        supNorm (U m k u - U m k w) ≤ m.lam ^ (k + 1) * supNorm (u - w) := by sorry

end ModPolicyIter.Conv
