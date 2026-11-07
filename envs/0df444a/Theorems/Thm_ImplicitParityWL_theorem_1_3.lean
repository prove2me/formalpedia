-- Prove2me | Theorems.Thm_ImplicitParityWL_theorem_1_3
-- name    : ImplicitParityWL.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:09:32.485294+00:00
-- url     : https://prove2.me/theorems/1092fc66-efc1-485b-851e-34216c12ba72
-- title:
--   Theorem 1.3 — $k$-WL distinguishes some $n$-vertex pairs only after $\Omega_k(n^{k-1})$ iterations
-- statement:
--   Let $k\ge3$ be fixed. For every $n_0\in\mathbb N$ there are some $n\ge n_0$ and $n$-vertex graphs $G_0,G_1$ such that $k$-WL distinguishes between $G_0$ and $G_1$, but only after $\Omega_k(n^{k-1})$ iterations. That is, there is $c>0$ depending on $k$ alone such that for every $n_0$ there are $n\ge n_0$, graphs $G_0,G_1$ on $n$ vertices and a round $T$ with
--   $$
--   \chi^{(T)}\text{-histograms of }G_0,G_1\text{ different},\quad \chi^{(r)}\text{-histograms equal for all }r<T,\quad c\,n^{k-1}\le T.
--   $$
--   This matches the known upper bound $O(n^{k-1})$ for $k\ge3$ up to constants depending on $k$, and it improves the previous lower bound $\Omega_k(n^{k/2})$ for graphs.
--
--   **Formalization Note** $k$-WL is the published `OAI.VariableWL.histogram`, the joint update of §3 with canonical colors.
--
--   Differences from the source:
--   - reading: n-vertex graphs, in a paper whose §3 opens with colored graphs and whose §6 ends with colored G_ε → uncolored simple graphs on Fin n; reason: the stronger reading: the introduction contrasts the result with k-ary relational structures that do not apply to graphs, and footnote 3 removes the colors; the colored statement follows with one color and is also theorem_1_3_colored
--   - encoding: only after Ω_k(n^{k−1}) iterations → ∃ c > 0 before n₀, T is the first distinguishing round, c * n ^ (k − 1) ≤ T; reason: the page's asymptotic with its quantifiers written out; the pair form, not the stabilization time of one graph
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Theorem 1.3, p.3, restated p.35

import Mathlib
import Definitions.Def_VariableWL

namespace ImplicitParityWL

/-- **Theorem 1.3** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.3, restated p.35): let `k ≥ 3` be fixed. For every `n₀ ∈ ℕ` there are some `n ≥ n₀` and `n`-vertex
graphs `G₀`, `G₁` such that `k`-WL distinguishes between `G₀` and `G₁`, but only after `Ω_k(n^{k-1})` iterations.

**Formalization Note** The constant `c > 0` of `Ω_k` depends on `k` alone: it is chosen before `n₀`. `T` is the first
distinguishing round: the histograms differ at `T` and agree at every earlier round. The graphs are uncolored simple graphs,
and `k`-WL is the published `OAI.VariableWL.histogram`, the joint update of §3 with canonical colors. -/
theorem theorem_1_3 (k : ℕ) (hk : 3 ≤ k) : ∃ c : ℝ, 0 < c ∧ ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧
    ∃ (G₀ G₁ : SimpleGraph (Fin n)) (T : ℕ),
      OAI.VariableWL.histogram ⟨n, G₀⟩ k T ≠ OAI.VariableWL.histogram ⟨n, G₁⟩ k T ∧
      (∀ r < T, OAI.VariableWL.histogram ⟨n, G₀⟩ k r = OAI.VariableWL.histogram ⟨n, G₁⟩ k r) ∧
      c * (n : ℝ) ^ (k - 1) ≤ (T : ℝ) := by sorry

end ImplicitParityWL
