-- Prove2me | Theorems.Thm_OnlineCRS_Submod_lemma_3_6
-- name    : OnlineCRS.Submod.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:26.016444+00:00
-- url     : https://prove2.me/theorems/8fe9db96-c6b6-47a9-9c7c-a2225aa9b62b
-- title:
--   Lemma 3.6, p. 17 (FMV Lemma 2.2) — E[g(T_p)] ≥ (1 − p)g(∅) + p·g(T) for correlated T_p
-- statement:
--   Let $g:2^N\to\mathbb R$ be a submodular function, $T\subseteq N$ and $p\in[0,1]$. Let $T_p\subseteq T$ be a random set that contains every element of $T$ with probability exactly $p$, not necessarily independently. Then
--   $$\mathbb E[g(T_p)]\ge(1-p)\,g(\varnothing)+p\cdot g(T).$$
--
--   This is Lemma 2.2 of Feige, Mirrokni and Vondrák. In the proof of Theorem 1.10 it bounds the loss from keeping each element of a fixed set with probability $1/2$.
--
--   **Formalization Note** The law of $T_p$ is an arbitrary probability vector $\mu$ on the subsets of $N$, supported on subsets of $T$, with marginals $\sum_{B\ni e}\mu(B)=p$ for every $e\in T$. The range $p\in[0,1]$ is stated explicitly. A published item of another mission (`NonmonotoneSubmod.RandomSet.lemma_2_2_sample_subset`) covers only the independent sample; this statement allows arbitrary correlation.
-- source:
--   arXiv:1508.00142v2, Lemma 3.6, p. 17 (Lemma 2.2 of Feige, Mirrokni, Vondrák, SIAM J. Comput. 40(4), 2011)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace OnlineCRS.Submod

open Classical in
/-- Lemma 3.6 (arXiv:1508.00142v2, p. 17; Lemma 2.2 of Feige–Mirrokni–Vondrák): let `g` be submodular and
`T ⊆ N`. For every random set `T_p ⊆ T`, with law `μ`, containing every element of `T` with probability
`p` (not necessarily independently), `E[g(T_p)] ≥ (1 − p) g(∅) + p · g(T)`. -/
theorem lemma_3_6 {α : Type} [Fintype α] [DecidableEq α] (g : Finset α → ℝ)
    (hg : NonmonotoneSubmod.Shared.Submodular g) (T : Finset α) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (μ : Finset α → ℝ) (hμ0 : ∀ B, 0 ≤ μ B) (hμ1 : ∑ B : Finset α, μ B = 1)
    (hμT : ∀ B, μ B ≠ 0 → B ⊆ T)
    (hμp : ∀ e ∈ T, ∑ B : Finset α, μ B * (if e ∈ B then 1 else 0) = p) :
    (1 - p) * g ∅ + p * g T ≤ ∑ B : Finset α, μ B * g B := by sorry

end OnlineCRS.Submod
