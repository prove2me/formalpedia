-- Prove2me | Theorems.Thm_MultitaskContracts_lemma_14
-- name    : MultitaskContracts.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:32:37.424391+00:00
-- url     : https://prove2.me/theorems/f0ff6de0-7b93-4bd2-a124-761b5427331f
-- title:
--   Lemma 14 — best responses to a separable contract decompose task by task
-- statement:
--   Let $I$ be an instance of the multitask model (any dependence) and let $t(Y)=t_0+\sum_{k\in Y}t_k$ be a separable contract with $t_0\ge0$ and $t_k\ge0$. A strategy $S$ is a best response to $t$ if and only if, for every task $k$, $\mathbf 1[k\in S]$ is a best response to the single-task contract paying $t_k$ on success when $k$ is the only task. In the single-task problem effort earns $p_kt_k-c_k$ and shirking earns $q_kt_k$, so the condition reads: for every $k$,
--   $$k\in S\ \Rightarrow\ p_kt_k-c_k\ \ge\ q_kt_k,\qquad k\notin S\ \Rightarrow\ q_kt_k\ \ge\ p_kt_k-c_k.$$
--
--   It reduces the separable benchmark to $|K|$ independent one-task problems.
--
--   Differences from the source:
--   - encoding: "1[k ∈ S] is a best response to the single-task contract paying t_k on success" → the weak inequality between the single-task utilities p_k t_k − c_k (effort) and q_k t_k (shirking); reason: these are the two utilities of the one-task problem with the same p_k, q_k, c_k
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Lemma 14, App. C, p.55 (PDF p.57)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Lemma 14** (App. C, p.55, PDF 57). A strategy `S` is a best response to a separable contract
`t(Y) = t₀ + ∑_{k∈Y} t_k` (`t₀ ≥ 0`, `t_k ≥ 0`) if and only if, for every task `k`, `1[k ∈ S]` is
a best response to the single-task contract paying `t_k` on success when `k` is the only task.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Lemma 14, p.55.

**Formalization Note.** In the single-task problem of task `k` (success probability `p_k` under
effort, `q_k` under shirking, cost `c_k`, pay `t_k` on success and `0` on failure) effort yields
`p_k t_k − c_k` and shirking `q_k t_k`; "`1[k ∈ S]` is a best response" is the corresponding
weak inequality. -/
theorem lemma_14 (I : Instance K) (t₀ : ℝ) (tk : K → ℝ) (ht₀ : 0 ≤ t₀) (htk : ∀ k, 0 ≤ tk k)
    (S : Finset K) :
    I.Implements (fun Y => t₀ + ∑ k ∈ Y, tk k) S ↔
      ∀ k, (k ∈ S → I.q k * tk k ≤ I.p k * tk k - I.c k) ∧
        (k ∉ S → I.p k * tk k - I.c k ≤ I.q k * tk k) := by sorry

end MultitaskContracts
