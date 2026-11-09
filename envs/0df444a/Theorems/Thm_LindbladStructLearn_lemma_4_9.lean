-- Prove2me | Theorems.Thm_LindbladStructLearn_lemma_4_9
-- name    : LindbladStructLearn.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:09:09.649566+00:00
-- url     : https://prove2.me/theorems/98aa7007-a96b-4d9c-ac9f-c17009b373a2
-- title:
--   Lemma 4.9 — Algorithm 2 is an unbiased estimator of $E^{(\ell)}_{\overline P}(x)$ bounded by $\ell!(2kg)^\ell$
-- statement:
--   Let $k \ge 1$, $g > 0$ and let $x$ be a vector on the $k$-local pairs with $\|x\|_{B_1} \le g$. For every integer $\ell \ge 0$ and every pair $\overline P$ with $s_{\overline P} \le k$, the output $Z^{(\ell)}_{\overline P}(x)$ of Algorithm 2 satisfies
--
--   $$\mathbb E\big[Z^{(\ell)}_{\overline P}(x)\big] = E^{(\ell)}_{\overline P}(x) \qquad\text{and}\qquad \big|Z^{(\ell)}_{\overline P}(x)\big| \le \ell!\,(2kg)^\ell$$
--
--   on every outcome of positive probability.
--
--   Algorithm 2 lets the learner estimate the higher Taylor coefficients of $E(x)$ classically, by sampling one term of the cluster expansion at a time.
--
--   Differences from the source:
--   - generalization: L_x a k-local Lindbladian → x any vector on the k-local pairs with P1 ≠ I (no positivity or imaginarity); reason: the paper applies the lemma to iterates, which need not be valid Lindbladians (p.41); the proof uses only k-locality and ‖x‖_B1 ≤ g
--   - encoding: the random output Z and its expectation → the finite output law of Algorithm 2 (list of probability–value pairs); the bound on every outcome of positive probability; reason: the randomness of Algorithm 2 is finite
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Lemma 4.9, p.31; Algorithm 2, p.30

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_alg2Law
import Definitions.Def_LindbladStructLearn_FinDist_expect
import Definitions.Def_LindbladStructLearn_Eell
import Definitions.Def_LindbladStructLearn_ext
import Definitions.Def_LindbladStructLearn_b1Norm

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Lemma 4.9 (unbiased estimator of `E^(ℓ)_P̄(x)`; Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.31, with Algorithm 2, p.30): for a
`k`-local `L_x` with `‖x‖_B1 ≤ g`, every integer `ℓ ≥ 0` and every `k`-local pair `P̄`, the output
`Z^(ℓ)_P̄(x)` of Algorithm 2 satisfies `E[Z^(ℓ)_P̄(x)] = E^(ℓ)_P̄(x)` and `|Z^(ℓ)_P̄(x)| ≤ ℓ!(2kg)^ℓ`.

**Formalization Note** `x ∈ ℂ^m` is any vector on the `k`-local pairs with `P₁ ≠ I` (the paper
applies the lemma to iterates, p.41). The law of `Z` is `alg2Law` (a finite list of
(probability, value) pairs); the bound holds on every outcome of positive probability.
`k, g > 0` is the paper's standing assumption (p.13). -/
theorem lemma_4_9 {n k : ℕ} (hk : 0 < k) (g : ℝ) (hg : 0 < g) (x : Idx n k → ℂ)
    (hx : b1Norm (ext x) ≤ g) (ℓ : ℕ) (P : Pauli n × Pauli n) (hP : (pairSupport P).card ≤ k) :
    FinDist.expect (alg2Law x P ℓ) id = Eell ℓ (ext x) P ∧
      ∀ o ∈ alg2Law x P ℓ, 0 < o.1 → ‖o.2‖ ≤ (ℓ.factorial : ℝ) * (2 * k * g) ^ ℓ := by sorry

end LindbladStructLearn
