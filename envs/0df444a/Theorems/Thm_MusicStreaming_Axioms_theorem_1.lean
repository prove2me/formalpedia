-- Prove2me | Theorems.Thm_MusicStreaming_Axioms_theorem_1
-- name    : MusicStreaming.Axioms.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:21.195145+00:00
-- url     : https://prove2.me/theorems/41baa062-3df6-4928-9ab7-e4d05fe8b777
-- title:
--   Theorem 1, p. 12 — homogeneity and additivity characterize weighted indices; with equal individual / global impact, pro-rata / user-centric
-- statement:
--   Let a **popularity index** be an index $I$ that, on every problem with at least one user, is a nonnegative vector over the artists with positive sum. Indices are identified with their positive multiples, since $R^{cI}=R^I$ for $c>0$ (p. 8).
--
--   1. **(a)** An index satisfies homogeneity and additivity if and only if it is a weighted index: there is a weight system $\omega>0$ with $I=I^\omega$ on every problem.
--   2. **(b)** If there are at least two artists, an index satisfies homogeneity, additivity and equal individual impact of similar users if and only if it is the pro-rata index:
--   $$\exists\,c>0\ \ \forall (N,M,t):\quad I(N,M,t)=c\,P(N,M,t).$$
--   3. **(c)** An index satisfies homogeneity, additivity and equal global impact of users if and only if it is the user-centric index:
--   $$\exists\,c>0\ \ \forall (N,M,t):\quad I(N,M,t)=c\,U(N,M,t).$$
--
--   The theorem gives normative grounds for the two indices used in practice: pro-rata and user-centric arise from the family of weighted indices by one further axiom each, the first equalizing streams and the second equalizing users.
--
--   **Formalization Note** "Is the pro-rata (user-centric) index" is read as being a positive multiple of it, with one constant $c$ for all problems. The hypothesis of at least two artists in (b) is added: with one artist the user-centric index $U_1=m$ satisfies the three axioms of (b) and is not a multiple of pro-rata; there every index pays the whole $m$ to the single artist, so (b) still holds at the level of rewards. Parts (a) and (c) hold for every $n$. Additivity is over disjoint user sets. Artists are indexed $0,\dots,n-1$ (index $i$ is the paper's artist $i+1$). Users are named by natural numbers, and a problem is a finitely supported table $t:\mathbb N\to\mathbb N^{N}$ whose support is the user set $M$; so every user in $M$ has played some artist ($L^j\neq\varnothing$, the paper's standing assumption, p. 19), streams are natural numbers, and the problem with $M\setminus\{j\}$ and $t_{-j}$ is $t$ with column $j$ erased.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 12, Theorem 1 (a)–(c); proof pp. 18–20

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

namespace MusicStreaming.Axioms

theorem theorem_1 :
    (∀ (n : ℕ) (I : Index n), IsIndex I →
      (Homogeneity I ∧ Additivity I ↔
        ∃ ω : ℕ → (Fin n → ℕ) → ℝ, (∀ j x, 0 < ω j x) ∧ ∀ t, I t = weightedIndex ω t)) ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ I : Index n, IsIndex I →
      (Homogeneity I ∧ Additivity I ∧ EqualIndividualImpact I ↔
        ∃ c : ℝ, 0 < c ∧ ∀ t, I t = c • proRata t)) ∧
    (∀ (n : ℕ) (I : Index n), IsIndex I →
      (Homogeneity I ∧ Additivity I ∧ EqualGlobalImpact I ↔
        ∃ c : ℝ, 0 < c ∧ ∀ t, I t = c • userCentric t)) := by sorry

end MusicStreaming.Axioms
