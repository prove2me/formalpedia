-- Prove2me | Theorems.Thm_OnlineCRS_Submod_lemma_3_7
-- name    : OnlineCRS.Submod.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:19:28.879151+00:00
-- url     : https://prove2.me/theorems/abbdf63e-f477-47d2-a617-54bfd93a3444
-- title:
--   Lemma 3.7, p. 17 (BFNS Lemma 2.2) — E[g(N_p)] ≥ (1 − p)g(∅) when every element has probability at most p
-- statement:
--   Let $g:2^N\to\mathbb R_{\ge0}$ be a non-negative submodular function and $p\in[0,1]$. Let $N_p\subseteq N$ be a random set that contains every element of $N$ with probability at most $p$, not necessarily independently. Then
--   $$\mathbb E[g(N_p)]\ge(1-p)\,g(\varnothing).$$
--
--   This is Lemma 2.2 of Buchbinder, Feldman, Naor and Schwartz. In the proof of Theorem 1.10 it controls the elements that the adversary can add to the half-sampled set.
--
--   **Formalization Note** The law of $N_p$ is an arbitrary probability vector $\mu$ on the subsets of $N$ with $\sum_{B\ni e}\mu(B)\le p$ for every $e$. The range $p\in[0,1]$ is stated explicitly.
-- source:
--   arXiv:1508.00142v2, Lemma 3.7, p. 17 (Lemma 2.2 of Buchbinder, Feldman, Naor, Schwartz, SODA 2014)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace OnlineCRS.Submod

open Classical in
/-- Lemma 3.7 (arXiv:1508.00142v2, p. 17; Lemma 2.2 of Buchbinder–Feldman–Naor–Schwartz): let `g ≥ 0` be
submodular. For every random set `N_p ⊆ N`, with law `μ`, containing every element of `N` with probability
at most `p` (not necessarily independently), `E[g(N_p)] ≥ (1 − p) g(∅)`. -/
theorem lemma_3_7 {α : Type} [Fintype α] [DecidableEq α] (g : Finset α → ℝ) (hg0 : ∀ S, 0 ≤ g S)
    (hg : NonmonotoneSubmod.Shared.Submodular g) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (μ : Finset α → ℝ) (hμ0 : ∀ B, 0 ≤ μ B) (hμ1 : ∑ B : Finset α, μ B = 1)
    (hμp : ∀ e : α, ∑ B : Finset α, μ B * (if e ∈ B then 1 else 0) ≤ p) :
    (1 - p) * g ∅ ≤ ∑ B : Finset α, μ B * g B := by sorry

end OnlineCRS.Submod
