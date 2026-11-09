-- Prove2me | Theorems.Thm_MaoLowDegree_Counterexample_lemma_3_1
-- name    : MaoLowDegree.Counterexample.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:10.612231+00:00
-- url     : https://prove2.me/theorems/6f556899-335e-44b0-b6e1-ec6aeebcd781
-- title:
--   Lemma 3.1 — random puncturing
-- statement:
--   There exists a positive absolute constant $\gamma_0$ with the following property. Let $s(T)$ be any integer-valued sequence tending to infinity, with $s(T)<\gamma_0T$ eventually, and fix $\delta_0\in(0,1)$. Choose $Z$ uniformly among the subsets of $\mathbb F_2^T$ of size $\lfloor(1-\delta_0)\sum_{j=0}^{s(T)}\binom Tj\rfloor$. Then
--   $$\Pr\{(\Psi_{s(T)}(z))_{z\in Z}\text{ is linearly independent over }\mathbb F_2\}\longrightarrow1\quad(T\longrightarrow\infty).$$
--
--   This is the external result quoted as [BHSS22, Theorem 1.1 and Corollary 4.1]. It retains arbitrary diverging degree sequences, not only the proportional degrees used by the rank test. Sampling is without replacement.
--
--   Differences from the source:
--   - encoding: for all sufficiently large n and probability 1-o(1) → Filter.atTop eventual assertions and Tendsto to 1; reason: these are the literal asymptotic quantifiers, with all fixed parameters before n
--   - encoding: integers s(T) tending to infinity and a uniform subset of prescribed size → natural degree sequence and uniform powersetCard law, with point mass at empty set only for impossible sizes; reason: a diverging integer sequence is eventually nonnegative; the prescribed subset size is always feasible for delta in (0,1)
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), Lemma 3.1 [BHSS22, Theorem 1.1 and Corollary 4.1], p.12

import Definitions.Def_MaoLowDegree_Counterexample_computationalClaims

open Classical Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Lemma 3.1 [BHSS22, Theorem 1.1 and Corollary 4.1], p.12.
Arbitrary diverging integer degree sequences and every fixed δ ∈ (0,1). -/
theorem lemma_3_1 :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ Puncturing γ₀ := by sorry

end MaoLowDegree.Counterexample
