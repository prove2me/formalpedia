-- Prove2me | Theorems.Thm_MusicStreaming_Axioms_theorem_1a
-- name    : MusicStreaming.Axioms.theorem_1a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:15.560986+00:00
-- url     : https://prove2.me/theorems/5e67ad45-76a0-4c11-8c91-33410ffdbf64
-- title:
--   Theorem 1(a), p. 12 — an index satisfies homogeneity and additivity iff it is a weighted index
-- statement:
--   Let $I$ be a popularity index: on every problem with at least one user, $I$ is a nonnegative vector over the artists with positive sum. Then $I$ satisfies homogeneity and additivity if and only if there is a weight system $\omega$, with $\omega(j,x)>0$ for every user $j$ and every profile $x\in\mathbb N^N$, such that for every problem $(N,M,t)$
--   $$I(N,M,t)=I^\omega(N,M,t),\qquad I^\omega_i(N,M,t)=\sum_{j\in M}\omega(j,t_{\cdot j})\,t_{ij}.$$
--
--   This is the characterization of the family of weighted indices; parts (b) and (c) of Theorem 1 single out pro-rata and user-centric inside it.
--
--   **Formalization Note** One weight system serves every problem. Weights at the zero profile never enter $I^\omega$ (no user of a problem has a zero profile) and are only required to be positive. Artists are indexed $0,\dots,n-1$ (index $i$ is the paper's artist $i+1$). Users are named by natural numbers, and a problem is a finitely supported table $t:\mathbb N\to\mathbb N^{N}$ whose support is the user set $M$; so every user in $M$ has played some artist ($L^j\neq\varnothing$, the paper's standing assumption, p. 19), streams are natural numbers, and the problem with $M\setminus\{j\}$ and $t_{-j}$ is $t$ with column $j$ erased.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 12, Theorem 1(a)

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

namespace MusicStreaming.Axioms

theorem theorem_1a {n : ℕ} (I : Index n) (hI : IsIndex I) :
    Homogeneity I ∧ Additivity I ↔
      ∃ ω : ℕ → (Fin n → ℕ) → ℝ, (∀ j x, 0 < ω j x) ∧ ∀ t, I t = weightedIndex ω t := by sorry

end MusicStreaming.Axioms
