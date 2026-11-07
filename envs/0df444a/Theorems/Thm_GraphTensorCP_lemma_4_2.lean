-- Prove2me | Theorems.Thm_GraphTensorCP_lemma_4_2
-- name    : GraphTensorCP.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:57.765165+00:00
-- url     : https://prove2.me/theorems/8797056b-e4c5-454b-a38a-497490b5eb55
-- title:
--   Lemma 4.2 — the profile is positive and symmetric, $P_\phi(1,\dots,1,b)=b$, $P_\phi(a)\le(1+\sum_j(a_j-1))^{1/t_\phi}$
-- statement:
--   For every integer $n\ge3$ and every spectral point $\phi\in\Phi_{n,\mathbb F}$:
--
--   1. the profile $P_\phi(a_1,\dots,a_{n-1})$ is positive for all positive integers $a_1,\dots,a_{n-1}$;
--   2. it is symmetric in its $n-1$ arguments;
--   3. $P_\phi(1,\dots,1,b)=b$ for every positive integer $b$;
--   4. $$P_\phi(a_1,\dots,a_{n-1})\le\Big(1+\sum_{j=1}^{n-1}(a_j-1)\Big)^{1/t_\phi}$$ for all positive integers $a_1,\dots,a_{n-1}$.
--
--   These are the normalization and interpolation upper bound against which the growth of the profile is compared.
--
--   **Formalization Note** Symmetry is invariance under every permutation of the arguments. $(1,\dots,1,b)$ places $b$ at the last argument (0-based index $n-2$). The hypothesis `hn : 1 < n` only types the spectrum and follows from $n\ge3$.
--
--   Differences from the source:
--   - encoding: spectral points $\phi:\mathrm{Tens}_n(\mathbb F)\to\mathbb R_{\ge0}$ (Definition 2.19) → monotone semiring homomorphisms on the published quotient `MME.TensorQ` by mutual restriction (`Spec K n hn`); reason: a spectral point is constant on mutual-restriction classes and its four conditions are exactly "monotone semiring homomorphism"; same set of maps
--   - encoding: arguments $a_1,\dots,a_{n-1}$ → $a:\mathrm{Fin}(n-1)\to\mathbb N$, last argument at index $n-2$; reason: relabeling
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Lemma 4.2, p.35

import Mathlib
import Definitions.Def_GraphTensorCP_profile

universe u

namespace GraphTensorCP

/-- **Lemma 4.2** (basic properties of the profile), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.35:
"For every integer n ≥ 3 and every spectral point ϕ ∈ Φ_{n,F}, the profile in Definition 4.1 is
positive and symmetric in its n − 1 arguments. For every positive integer b and all positive integers
a₁, . . . , a_{n−1}, it satisfies P_ϕ(1, . . . , 1, b) = b, P_ϕ(a₁, . . . , a_{n−1}) ≤
( 1 + Σ_{j=1}^{n−1}(a_j − 1) )^{1/t_ϕ}."

**Formalization Note.** `hn : 1 < n` only types the spectrum `Spec K n hn`; it follows from
`hn3 : 3 ≤ n`. The arguments are `a : Fin (n−1) → ℕ`, positive and symmetric statements are over
positive tuples, symmetry is invariance under every permutation `σ` of the `n − 1` arguments, and
`(1, …, 1, b)` puts `b` at the last argument `n − 2` (0-based). -/
theorem lemma_4_2 {K : Type u} [Field K] {n : ℕ} (hn : 1 < n) (hn3 : 3 ≤ n) (φ : Spec K n hn) :
    (∀ a : Fin (n - 1) → ℕ, (∀ j, 0 < a j) → 0 < profile φ a) ∧
    (∀ (σ : Equiv.Perm (Fin (n - 1))) (a : Fin (n - 1) → ℕ), (∀ j, 0 < a j) →
      profile φ (a ∘ σ) = profile φ a) ∧
    (∀ b : ℕ, 0 < b →
      profile φ (Function.update (fun _ => 1) ⟨n - 2, by omega⟩ b) = (b : ℝ)) ∧
    (∀ a : Fin (n - 1) → ℕ, (∀ j, 0 < a j) →
      profile φ a ≤ ((1 + ∑ j, (a j - 1) : ℕ) : ℝ) ^ (1 / tPhi φ)) := by sorry

end GraphTensorCP
