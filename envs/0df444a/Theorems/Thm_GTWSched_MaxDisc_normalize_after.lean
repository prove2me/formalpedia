-- Prove2me | Theorems.Thm_GTWSched_MaxDisc_normalize_after
-- name    : GTWSched.MaxDisc.normalize_after
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:50:23.423769+00:00
-- url     : https://prove2.me/theorems/0102d78a-6598-48ca-ac25-e635d1ff350b
-- title:
--   §3.1, p. 344 — after T_N: no idle time and nondecreasing deadlines, without moving T_N later
-- statement:
--   Let $N$ tasks have lengths $l_i \ge 0$, release times $r_i \ge 0$ and deadlines $d_i$ in special form for $\alpha \ge 0$, indexed so that $d_0 \le d_1 \le \dots \le d_{N-1}$, and let $T_n$ be the last task, $n = N - 1$. Let $(\sigma, s)$ be an optimum schedule with the release time property with respect to $T_n$. Then there is an optimum schedule $(\sigma'', s'')$ such that:
--
--   1. it has the release time property with respect to $T_n$, and $T_n$ occupies the same position as in $(\sigma, s)$;
--   2. the tasks before $T_n$ are executed in the same order and at the same times as in $(\sigma, s)$;
--   3. $T_n$ starts no later than before, $s''_n \le s_n$, and in fact as early as possible: $$s''_n = \max\Big(r_n,\ \max_{T_i \text{ before } T_n} (s_i + l_i)\Big),$$ with the inner maximum $0$ when no task precedes $T_n$;
--   4. the tasks after $T_n$ are executed in increasing order of index (hence of nondecreasing deadline);
--   5. from the start of $T_n$ on there is no idle time: each later task starts when its predecessor finishes.
--
--   These are the transformations by which the paper passes from a schedule given by Corollary 1 to a schedule in standard form.
--
--   **Formalization Note.** Indices are 0-based; the paper's $T_N$ is the index $N-1$, expressed by a task $n$ with $n + 1 = N$.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 344, paragraph after the proof of COROLLARY 1 ("This immediately implies that there can be no idle time …") and the paragraph before COROLLARY 2 ("The necessary transformations …")

import Mathlib
import Definitions.Def_GTWSched_MaxDisc_Model

namespace GTWSched.MaxDisc

theorem normalize_after {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (hd : Monotone d) (n : Fin N) (hnlast : n.val + 1 = N)
    (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (hopt : Optimum r d l σ s) (hrtp : ReleaseTimeProperty r σ s n) :
    ∃ (σ' : Fin N ≃ Fin N) (s' : Fin N → ℝ),
      Optimum r d l σ' s' ∧ ReleaseTimeProperty r σ' s' n ∧
      σ'.symm n = σ.symm n ∧
      (∀ p : Fin N, p < σ.symm n → σ' p = σ p ∧ s' (σ p) = s (σ p)) ∧
      s' n ≤ s n ∧
      s' n = max (r n) (⨆ i : {i : Fin N // σ'.symm i < σ'.symm n}, s' i.1 + l i.1) ∧
      (∀ p q : Fin N, σ'.symm n < p → p < q → σ' p < σ' q) ∧
      (∀ p q : Fin N, σ'.symm n ≤ p → q.val = p.val + 1 →
        s' (σ' q) = s' (σ' p) + l (σ' p)) := by sorry

end GTWSched.MaxDisc
