-- Prove2me | Theorems.Thm_LindbladStructLearn_lemma_4_10
-- name    : LindbladStructLearn.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:12:29.055209+00:00
-- url     : https://prove2.me/theorems/2ab3c307-eaf3-46af-9b54-ba60b123abad
-- title:
--   Lemma 4.10 — Algorithm 3 is an unbiased estimator of the truncated series $\widetilde E_{\overline P}(x)$
-- statement:
--   Let $k \ge 1$, $g > 0$, $t > 0$, and let $x$ be a vector on the $k$-local pairs with $\|x\|_{B_1} \le g$. For every threshold $\Gamma \in \mathbb N$ and every pair $\overline P$ with $s_{\overline P} \le k$, the output $Y_{\overline P}(x)$ of Algorithm 3 satisfies
--
--   $$\mathbb E\big[Y_{\overline P}(x)\big] = \widetilde E_{\overline P}(x) = \sum_{\ell=1}^{\Gamma}\frac{t^\ell}{\ell!}E^{(\ell)}_{\overline P}(x),$$
--
--   and $|Y_{\overline P}(x)| \le (4kgt)^\ell$ for the degree $\ell$ sampled in Algorithm 3, on every outcome of positive probability.
--
--   For $t < 1/(4kg)$ the estimator is bounded by $1$, so averages of independent copies concentrate.
--
--   Differences from the source:
--   - generalization: L_x a k-local Lindbladian → x any vector on the k-local pairs with P1 ≠ I; reason: the lemma is applied to iterates (p.41); the proof uses only Lemma 4.9
--   - reading: any threshold Γ ≥ 0 (Algorithm 3's input Γ ∈ ℕ ∪ {+∞}) → Γ ∈ ℕ; reason: for Γ = +∞ and large t the expectation of Y need not exist; the algorithm uses finite Γ ((5.79))
--   - encoding: the random output (ℓ, Y) and its expectation → the finite output law of Algorithm 3; the bound on every outcome of positive probability; reason: the randomness of Algorithm 3 is finite
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Lemma 4.10, p.32; Algorithm 3, p.32

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_alg3Law
import Definitions.Def_LindbladStructLearn_FinDist_expect
import Definitions.Def_LindbladStructLearn_Etrunc
import Definitions.Def_LindbladStructLearn_ext
import Definitions.Def_LindbladStructLearn_b1Norm

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Lemma 4.10 (unbiased estimator of `Ẽ_P̄(x)`; Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.32, with Algorithm 3, p.32): for a
`k`-local `L_x` with `‖x‖_B1 ≤ g`, every threshold `Γ ≥ 0` and every `k`-local pair `P̄`, the output
`Y_P̄(x)` of Algorithm 3 satisfies `E[Y_P̄(x)] = Ẽ_P̄(x)` and `|Y_P̄(x)| ≤ (4kgt)^ℓ` for the degree
`ℓ` sampled in Algorithm 3.

**Formalization Note** `x` is any vector on the `k`-local pairs with `P₁ ≠ I`; `t > 0` is
Algorithm 3's input; `Γ` is a natural number. The law of `(ℓ, Y)` is `alg3Law`; the bound holds on
every outcome of positive probability. `k, g > 0` is the paper's standing assumption (p.13). -/
theorem lemma_4_10 {n k : ℕ} (hk : 0 < k) (g : ℝ) (hg : 0 < g) (x : Idx n k → ℂ)
    (hx : b1Norm (ext x) ≤ g) (Γ : ℕ) (t : ℝ) (ht : 0 < t) (P : Pauli n × Pauli n)
    (hP : (pairSupport P).card ≤ k) :
    FinDist.expect (alg3Law x P Γ t) (fun o => o.2) = Etrunc Γ t (ext x) P ∧
      ∀ o ∈ alg3Law x P Γ t, 0 < o.1 → ‖o.2.2‖ ≤ (4 * k * g * t) ^ o.2.1 := by sorry

end LindbladStructLearn
