-- Prove2me | Theorems.Thm_FullPathSCC_eq_A_11_shift
-- name    : FullPathSCC.eq_A_11_shift
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:19.62527+00:00
-- url     : https://prove2.me/theorems/9eb2bfa0-b636-44d8-8bf7-8b5e4eccff68
-- title:
--   (A.11), proof of Theorem A.2 — adding $M$ to every $U_t$ adds $M(1-\beta^{N-t})/(1-\beta)$ to every full-path utility, so optimal plans coincide
-- statement:
--   Let $\bar K,\bar T,k>0$, $0<\beta<1$ and $N\in\mathbb N$, let $\mathcal S$ be a finite nonempty set of disaster states, and let the data $p$, $U_t$, $g_{K,t}$, $g_{T,t}$, $h$ satisfy the standing assumptions of §3.1 (see the definition `FullPathSCC.Model`). States are $x=(K,T,\vartheta)$ in the box $[0,\bar K]\times[0,\bar T]\times\mathcal S$; an action $(C,\mu)$ is admissible at $x$ when $0\le C\le K$ and $0\le\mu\le1$; $k_t=k\beta^t$. For $M\in\mathbb R$ let $\bar U_t=U_t+M$ (and $h$ unchanged), and write $J_t^\pi(x)[U]$ and $J_t^\pi(x)[\bar U]$ for the full-path utilities in the two models. For every $t\le N$, every $x$ in the box and every plan $\pi$ admissible from $(t,x)$,
--
--   $$
--   J_t^\pi(x)[U]=J_t^\pi(x)[\bar U]-\frac{1-\beta^{N-t}}{1-\beta}\,M .
--   $$
--
--   At $t=0$ this is (A.11). Hence an admissible plan from $(t,x)$ is optimal among the admissible plans for $\bar U$ if and only if it is optimal among them for $U$, which lets the paper apply results that assume nonnegative per-stage utilities.
--
--   Differences from the source:
--   - generalization: (A.11) at $t=0$, with factor $(1-\beta^N)/(1-\beta)$ → every $t\le N$, with factor $(1-\beta^{N-t})/(1-\beta)$; reason: $t=0$ is the instance
--   - generalization: $M$ of (A.8), so that $\bar U_t\ge0$ → any real $M$; reason: the identity does not use the value of $M$
--   - generalization: a policy is optimal for $\bar U$ if and only if it is optimal for $U$ → an admissible plan is optimal among all admissible plans for $\bar U$ if and only if it is for $U$, from every $(t,x)$; reason: policies are plans, and $t=0$ is the instance
--   - reading: $\beta^N h(C_N)$ in (A.5), (A.10), (A.11) → $\beta^{N-t}h$ at the terminal state $X_N=(K_N,T_N,\vartheta_N)$; reason: no control $C_N$ exists (controls run over $t\le N-1$) and $V_N\equiv h$ is the terminal value
--   - encoding: the expectation with respect to the measure induced by the dynamics (7), (8) and the plan → the finite sum over disaster paths $\omega\in\mathcal S^{N-t}$ weighted by $\prod_n p_{\vartheta_n,\omega_n}(T_n)$; reason: the chain on $\mathcal S$ is finite; same value
--   - encoding: admissible controls $(C_t,\mu_t)\in[0,K_t]\times[0,1]$ → deterministic plans depending on the realized disaster history, admissible along every history (including zero-probability ones); reason: changing a plan on zero-probability histories does not change its full-path utility
--   - reading: $K_t\in[0,\bar K]$, $T_t\in[0,\bar T]$ at every $t$ (§3.1), while $g_{K,t}:D_{K,t}\to\mathbb R$ and $g_{T,t}:D_{T,t}\to\mathbb R$ → $g_{K,t}$ maps $D_{K,t}$ into $[0,\bar K]$ and $g_{T,t}$ maps $D_{T,t}$ into $[0,\bar T]$ for $t<N$; reason: (8) evaluates $V_{t+1}$, and $V_N\equiv h$ given on $[0,\bar K]$, at $(g_{K,t},g_{T,t},j)$, so the next state must lie in the box where they are defined
--   - generalization: $g_{K,t}$, $g_{T,t}$, $p_{\vartheta,\hat\vartheta}$, $U_t$, $h$ of class $C^1$ → continuous on the same domains; reason: $C^1$ functions are continuous, so every model of §3.1 satisfies the hypotheses
--   - generalization: $U_t$ strictly increasing, with values in $\mathbb R_+$, and $U_t(0)=0$ → no monotonicity, sign or normalization condition on $U_t$; reason: dropped hypotheses: every utility of §3.1 is allowed
--   - generalization: $\mathcal S=\{1,2,3,4\}$ → any finite nonempty set of disaster states; reason: $\{1,2,3,4\}$ is an instance
--   - generalization: $h:[0,\bar K]\to\mathbb R$ of class $C^1$ → $h$ continuous in $(K,T)$ on $[0,\bar K]\times[0,\bar T]$ for each disaster state; reason: the paper's $h$ is the instance $h(K,T,\vartheta)=h(K)$
--   - encoding: $p_{\vartheta,\hat\vartheta}:[0,\bar T]\to[0,1]$ is the transition probability from $\vartheta$ to $\hat\vartheta$ → $p\ge0$ and $\sum_{\hat\vartheta}p_{\vartheta,\hat\vartheta}(T)=1$ for $T\in[0,\bar T]$; reason: what a transition probability is; $p\le1$ follows
--   - encoding: $U_t\in C^1([0,K_t])$ for the current capital $K_t$ → $U_t$ continuous on $[0,\bar K]$; reason: $K_t$ ranges over $[0,\bar K]$, so $U_t$ is needed on all of $[0,\bar K]$; continuity there is continuity on every $[0,K_t]$
--   - generalization: $\infty>N\ge1$ (proof of Theorem A.2, p.7601) → $N\ge0$; reason: $N=0$ only adds a trivial case
-- source:
--   Zhao, Basu, Lontzek & Schmedders, The Social Cost of Carbon When We Wish for Full-Path Robustness, Management Science 69(12) (2023), doi:10.1287/mnsc.2023.4736, proof of Theorem A.2, (A.11), p.7602

import Mathlib
import Definitions.Def_FullPathSCC_Model
import Definitions.Def_FullPathSCC_Model_obj
import Definitions.Def_FullPathSCC_Model_fullPathUtility

namespace FullPathSCC

open Model

/-- **(A.11), proof of Theorem A.2** (Management Science 69(12) (2023), p.7602): adding a constant
`M` to every per-stage utility (`Ū_t = U_t + M`, `h` unchanged; `M'` below is that model) changes
the full-path utility of every admissible plan by the same amount. For `t ≤ N`, `x` in the box and
`π` admissible from `(t, x)`: `J_t^π(x)[U] = J_t^π(x)[Ū] − ((1 − β^{N−t})/(1 − β)) M`. At `t = 0`
this is (A.11). Hence ("Hence, by (A.10), a policy is optimal for the preceding utility using
`Ū(·,·)` if and only if it is optimal for our original problem using `U(·,·)`") an admissible plan
is optimal among the admissible plans for `Ū` if and only if it is for `U`. -/
theorem eq_A_11_shift {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (M : Model S) (hM : M.Standing) (B : ℝ) (M' : Model S)
    (hM' : M' = { M with U := fun s C => M.U s C + B }) (t : ℕ) (ht : t ≤ M.N) (x : State S)
    (hx : M.InBox x) :
    (∀ π : Plan S, M.PlanAdmissible t x π →
      M.fullPathUtility t x π =
        M'.fullPathUtility t x π - (1 - M.β ^ (M.N - t)) / (1 - M.β) * B) ∧
    ∀ π : Plan S, M.PlanAdmissible t x π →
      ((∀ π' : Plan S, M'.PlanAdmissible t x π' →
          M'.fullPathUtility t x π' ≤ M'.fullPathUtility t x π) ↔
        ∀ π' : Plan S, M.PlanAdmissible t x π' →
          M.fullPathUtility t x π' ≤ M.fullPathUtility t x π) := by sorry

end FullPathSCC
