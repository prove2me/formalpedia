-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_conditional_squaring
-- name    : LinearHashingPoissonesque.ExpectedLoads.conditional_squaring
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-09T19:02:06.857386+00:00
-- url     : https://prove2.me/theorems/48921f2c-5ac7-4f78-84ba-b2464e7189a8
-- title:
--   Lemma 2 — centered potential conditional squaring
-- statement:
--   Fix $S\subseteq\mathbb F_2^u$, $\lambda\in\mathbb R$, and $i$ linearly independent vectors $v_1,\ldots,v_i$, with $0\le i<u$. Let $V_i$ be their span and choose $v_{i+1}$ uniformly from $\mathbb F_2^u\setminus V_i$. For the actual centered coset potential $\Phi_i$ defined above,
--
--   $$\mathbb E_{v_{i+1}}[\Phi_{i+1}(S;\lambda;v_{\le i+1})]\le\Phi_i(S;\lambda;v_{\le i})^2.$$
--
--   The prior tuple, the set and the real parameter are fixed in this expectation. The next center is $|S|/2^{u-i-1}$. This is the recurrence for the paper's kernel potential, including negative and zero $\lambda$.
--
--   Differences from the source:
--   - encoding: binary vectors and the fixed S and λ in the Section 3 preamble → BinaryVector u, a finite set S, real lam, tupleSpan and Fin.snoc; reason: coordinates and tuple appending express exactly the specified cosets and changing center
--   - encoding: sample vᵢ₊₁ uniformly outside Vᵢ → i < u and the sum of the next potentials over nextVectors v divided by its cardinality; reason: linearly independent i-tuples have a nonempty complement exactly when i < u; the nonempty sampling domain is implicit in the source
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.10, Lemma 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_KernelPotential

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Lemma 2, p.10, with fixed S and λ from the section preamble.
i < u is the implicit nonempty sampling domain in v_{i+1} ∼ F₂^u \ V_i. -/
theorem conditional_squaring {u i : ℕ} (hi : i < u)
    (S : Finset (BinaryVector u)) (lam : ℝ) (v : Fin i → BinaryVector u)
    (hv : LinearIndependent (ZMod 2) v) :
    (∑ w ∈ nextVectors v, kernelPotential S lam (Fin.snoc v w)) /
      ((nextVectors v).card : ℝ) ≤ (kernelPotential S lam v) ^ 2 := by sorry

end LinearHashingPoissonesque.ExpectedLoads
