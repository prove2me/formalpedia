-- Prove2me | Theorems.Thm_MusicStreaming_Axioms_additive_decomposition
-- name    : MusicStreaming.Axioms.additive_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:09.812067+00:00
-- url     : https://prove2.me/theorems/f449b6f4-2148-4cd8-8ed4-036cd9b7e4d9
-- title:
--   Appendix, proof of Theorem 1(a), p. 18 — an additive index is the sum of its values on the one-user problems
-- statement:
--   Let $I$ be an index satisfying additivity. Then for every problem $(N,M,t)$ and every artist $i$,
--   $$I_i(N,M,t)=\sum_{j\in M}I_i(N,\{j\},t_{\cdot j}),$$
--   where $(N,\{j\},t_{\cdot j})$ is the problem with the single user $j$ and that user's profile $t_{\cdot j}$.
--
--   This reduces any additive index to its values on one-user problems, which is the first step of the "only if" direction of Theorem 1(a).
--
--   **Formalization Note** Only additivity is assumed; on the empty problem both sides are $0$ (additivity applied to $0=0+0$ gives $I(\text{empty})=0$). Artists are indexed $0,\dots,n-1$ (index $i$ is the paper's artist $i+1$). Users are named by natural numbers, and a problem is a finitely supported table $t:\mathbb N\to\mathbb N^{N}$ whose support is the user set $M$; so every user in $M$ has played some artist ($L^j\neq\varnothing$, the paper's standing assumption, p. 19), streams are natural numbers, and the problem with $M\setminus\{j\}$ and $t_{-j}$ is $t$ with column $j$ erased.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 18, Appendix, proof of Theorem 1(a), display "I_i(N, M, t) = Σ_{j∈M} I_i(N, {j}, t.j)"

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

namespace MusicStreaming.Axioms

theorem additive_decomposition {n : ℕ} (I : Index n) (hA : Additivity I) :
    ∀ (t : Problem n) (i : Fin n), I t i = ∑ j ∈ t.support, I (Finsupp.single j (t j)) i := by sorry

end MusicStreaming.Axioms
