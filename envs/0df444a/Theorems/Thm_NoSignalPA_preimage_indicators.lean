-- Prove2me | Theorems.Thm_NoSignalPA_preimage_indicators
-- name    : NoSignalPA.preimage_indicators
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T16:02:43.071969+00:00
-- url     : https://prove2.me/theorems/e6b22867-7a65-4c66-a317-8c2d2f27af77
-- title:
--   For a uniformly random $h$, the indicators $V_{\mathbf a}=[h(\mathbf a)=\mathbf k]$ are independent with $\Pr\{V_{\mathbf a}=1\}=2^{-N_s}$
-- statement:
--   Fix $\mathbf k\in\{0,1\}^{N_s}$ and pick $h:\{0,1\}^{N_r}\to\{0,1\}^{N_s}$ uniformly at random. Let $V_{\mathbf a}=1$ if $h(\mathbf a)=\mathbf k$ (that is, $\mathbf a\in\mathcal A_{\mathbf k}$) and $V_{\mathbf a}=0$ otherwise. Then for every finite set $S$ of strings and every prescribed pattern $(v_{\mathbf a})_{\mathbf a\in S}$ of bits,
--
--   $$
--   \Pr\{V_{\mathbf a}=v_{\mathbf a}\ \text{for all }\mathbf a\in S\}=\prod_{\mathbf a\in S}q(v_{\mathbf a}),\qquad q(1)=2^{-N_s},\ q(0)=1-2^{-N_s}.
--   $$
--
--   That is, the $V_{\mathbf a}$ are independent and $\Pr\{V_{\mathbf a}=1\}=2^{-N_s}$ for all $\mathbf a$.
--
--   Differences from the source:
--   - encoding: the random variables V_a are independent and Prob{V_a = 1} = 2^{−Ns} → the joint law of every finite subfamily (V_a)_{a∈S} factorizes with marginals 2^{−Ns}, 1 − 2^{−Ns}; V_a is the Boolean [h(a) = k]; reason: for finitely many Bernoulli variables this factorization is the definition of independence with these marginals
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Appendix, proof of Lemma 2, p.5

import Mathlib
import Definitions.Def_NoSignalPA_Str
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability

namespace NoSignalPA

/-- **For a uniformly random `h`, the indicators `V_a = [h(a) = k]` are independent with
`Prob{V_a = 1} = 2^{−Ns}`.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Appendix, proof of Lemma 2, p. 5 (PDF p. 5): "Let `V_a = 1` if the string a belongs to
`A_k`, and `V_a = 0` otherwise. If we pick a random function h with uniform distribution over the
set of all functions, then the random variables `V_a` are independent and distributed according
to `Prob{V_a = 1} = 2^{−Ns}`, for all a."

For every key `k`, every finite set `S` of strings and every prescribed pattern `v`, the
probability that `V_a = v(a)` for all `a ∈ S` is `∏_{a∈S} q(v(a))`, with `q(1) = 2^{−Ns}`,
`q(0) = 1 − 2^{−Ns}`.

**Formalization Note.** `V_a` is the Boolean `decide (h a = k)`. Independence with these
marginals is stated as the factorization of the joint law of every subfamily
`(V_a)_{a∈S}`; `S = {a}` gives `Prob{V_a = 1} = 2^{−Ns}`. -/
theorem preimage_indicators {Nr Ns : ℕ} (k : Str Ns) (S : Finset (Str Nr))
    (v : Str Nr → Bool) :
    OAI.ThorpCompatibility.uniformProbability (fun h : Str Nr → Str Ns => ∀ a ∈ S, decide (h a = k) = v a)
      = ∏ a ∈ S, (if v a then ((2 : ℝ) ^ Ns)⁻¹ else 1 - ((2 : ℝ) ^ Ns)⁻¹) := by sorry

end NoSignalPA
