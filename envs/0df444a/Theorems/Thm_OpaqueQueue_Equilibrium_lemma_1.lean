-- Prove2me | Theorems.Thm_OpaqueQueue_Equilibrium_lemma_1
-- name    : OpaqueQueue.Equilibrium.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:07.016777+00:00
-- url     : https://prove2.me/theorems/8d989b7f-8df5-45f0-a4f2-bc2778374ad9
-- title:
--   Lemma 1, p. 13 (PDF 14) — necessary and sufficient conditions (10)–(13) for optimality in the customer's problem (9)
-- statement:
--   Fix the queue parameters under the standing assumptions, and let $g=(g_n)_{n\ge0}$ be any prior on the number of customers in the system: $g_n\ge0$, $\sum_n g_n=1$, with finite mean $\sum_n n\,g_n<\infty$. Write $e_n = e^{v_n/\theta}$. A number $x$ solves the customer's problem
--   $$\max_{x\in[0,1]}\ \theta\sum_{n\ge0}g_n\log\big(x e_n+1-x\big) \tag{9}$$
--   if and only if $x\in[0,1]$ and
--   $$\sum_{n=0}^{\infty}\frac{e_n\,g_n}{x e_n+1-x}\le1 \quad(\text{"Joining"}, (10)),\qquad \sum_{n=0}^{\infty}\frac{g_n}{x e_n+1-x}\le1\quad(\text{"Balking"}, (11)),$$
--   the second series converging, with equality in both when $0<x<1$. In particular
--
--   1. $x=0$ is optimal if and only if $\mathbb E_G[e^{v_n/\theta}]=\sum_n g_n e_n\le1$ (12);
--   2. $x=1$ is optimal if and only if $\mathbb E_G[e^{-v_n/\theta}]=\sum_n g_n e^{-v_n/\theta}$ is finite and at most $1$ (13).
--
--   The lemma characterizes when a rationally inattentive customer joins or balks with certainty and when she randomizes; it is the customer's best-response rule that the equilibrium analysis feeds a prior into.
--
--   **Formalization Note** The paper states the lemma for the joining policy $\Pi=\{\pi_n\}$ of problem (6); since the optimal $\pi_n$ are determined by $\bar\pi$ through (8), and the paper reduces (6) to (9) on p. 12, the lemma is formalized on problem (9) for the unconditional probability $x=\bar\pi$. The finite-mean hypothesis is added: at $x=1$ the objective is $\sum_n g_n v_n$, which is finite for every prior only under it. In (13) the convergence of $\sum_n g_ne^{-v_n/\theta}$ is part of the condition, because $v_n\to-\infty$.
-- source:
--   Canyakmaz & Boyacı, Opaque Queues: Service Systems with Rationally Inattentive Customers, ESMT Working Paper 18-04 (September 24, 2018), p. 13 (PDF 14), Lemma 1, eqs. (10)–(13); problem (9), p. 12 (PDF 13)

import Mathlib
import Definitions.Def_OpaqueQueue_Equilibrium_Model

namespace OpaqueQueue.Equilibrium
theorem lemma_1 (P : Params) (hS : P.Standing) (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hgs : Summable g) (hg1 : ∑' n, g n = 1) (hgm : Summable (fun n : ℕ => (n : ℝ) * g n)) : (∀ x : ℝ, IsOptimal P g x ↔ x ∈ Set.Icc (0 : ℝ) 1 ∧ (∑' n, Real.exp (v P n / P.θ) * g n / (x * Real.exp (v P n / P.θ) + 1 - x)) ≤ 1 ∧ (Summable (fun n : ℕ => g n / (x * Real.exp (v P n / P.θ) + 1 - x)) ∧ (∑' n, g n / (x * Real.exp (v P n / P.θ) + 1 - x)) ≤ 1) ∧ (0 < x → x < 1 → (∑' n, Real.exp (v P n / P.θ) * g n / (x * Real.exp (v P n / P.θ) + 1 - x)) = 1 ∧ (∑' n, g n / (x * Real.exp (v P n / P.θ) + 1 - x)) = 1)) ∧ (IsOptimal P g 0 ↔ (∑' n, g n * Real.exp (v P n / P.θ)) ≤ 1) ∧ (IsOptimal P g 1 ↔ Summable (fun n : ℕ => g n * Real.exp (-(v P n) / P.θ)) ∧ (∑' n, g n * Real.exp (-(v P n) / P.θ)) ≤ 1) := by sorry
end OpaqueQueue.Equilibrium
