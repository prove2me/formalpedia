-- Prove2me | Theorems.Thm_FullPathSCC_eq_A_10_verification
-- name    : FullPathSCC.eq_A_10_verification
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:33.40731+00:00
-- url     : https://prove2.me/theorems/d4af57f2-eae6-466a-b911-109fff02f921
-- title:
--   (A.10), proof of Theorem A.2 — a Bellman solution with a maximizing selector is the maximal full-path utility, attained by the selector
-- statement:
--   Let $\bar K,\bar T,k>0$, $0<\beta<1$ and $N\in\mathbb N$, let $\mathcal S$ be a finite nonempty set of disaster states, and let the data $p$, $U_t$, $g_{K,t}$, $g_{T,t}$, $h$ satisfy the standing assumptions of §3.1 (see the definition `FullPathSCC.Model`). States are $x=(K,T,\vartheta)$ in the box $[0,\bar K]\times[0,\bar T]\times\mathcal S$; an action $(C,\mu)$ is admissible at $x$ when $0\le C\le K$ and $0\le\mu\le1$; $k_t=k\beta^t$. Let $V_0,\dots,V_N$ be functions on states with $V_N=h$ on the box and, for $t<N$ and every $x$ in the box,
--
--   $$
--   V_t(x)=\max_{(C,\mu)\text{ admissible at }x}\mathrm{obj}_t(V_{t+1};x,(C,\mu))
--   $$
--
--   with the maximum attained, and let $\varphi$ be a Markov policy such that $\varphi_t(x)$ is admissible and attains this maximum. Then for every $t\le N$ and every $x$ in the box:
--
--   1. the plan induced by $\varphi$ from $(t,x)$ is admissible and $J_t^{\varphi}(x)=V_t(x)$;
--   2. every plan $\pi$ admissible from $(t,x)$ satisfies $J_t^\pi(x)\le V_t(x)$.
--
--   At $t=0$ this is (A.10): $V^*_0(K_0,T_0,\vartheta_0)=\max_{\{(C_t,\mu_t)\}}-\frac1k\ln E[\exp(-k(\sum_{t<N}\beta^tU_t(C_t)+\beta^Nh))]$, attained by $\varphi^*$.
--
--   Differences from the source:
--   - generalization: (A.10) at $t=0$ → every start time $t\le N$; reason: $t=0$ is the instance; the paper calls $\varphi^*$ subpath optimal
--   - generalization: $V^*$, $\varphi^*$ obtained in (A.9) → any $V$, $\varphi$ with $V_N=h$, (8) with attained maximum, and $\varphi$ selecting a maximizing admissible action; reason: (A.9)'s $V^*$, $\varphi^*$ satisfy these hypotheses
--   - generalization: the maximum over control sequences $\{(C_t,\mu_t)\}_{0\le t\le N-1}$ in (A.10), and Markov policies → every deterministic plan whose actions depend on the realized disaster history; reason: Markov policies are such plans; the bound $J\le V$ holds for the larger class
--   - encoding: a "Markov policy" (a measurable decision rule in the framework of Bäuerle and Rieder (2014), though neither Theorem A.2 nor (A.9) says measurable, and the paper writes "for some function") → $\varphi$ an arbitrary function of $(t,K,T,\vartheta)$; reason: from a fixed start state only finitely many states are reached along the finite chain, so no quantity of the statement depends on the measurability of $\varphi$
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
--   Zhao, Basu, Lontzek & Schmedders, The Social Cost of Carbon When We Wish for Full-Path Robustness, Management Science 69(12) (2023), doi:10.1287/mnsc.2023.4736, proof of Theorem A.2, (A.10), p.7602

import Mathlib
import Definitions.Def_FullPathSCC_Model
import Definitions.Def_FullPathSCC_Model_obj
import Definitions.Def_FullPathSCC_Model_fullPathUtility

namespace FullPathSCC

open Model

/-- **(A.10), proof of Theorem A.2** (Management Science 69(12) (2023), p.7602): verification. Let
`V` solve the Bellman equation (8) on the box with `V_N = h`, the maximum attained at every state,
and let `φ` be a Markov policy choosing an admissible maximizing action at every state and time
`t < N`. Then for every `t ≤ N` and every state `x` in the box: the plan induced by `φ` from
`(t, x)` is admissible and its full-path utility equals `V_t(x)`, and every plan admissible from
`(t, x)` has full-path utility at most `V_t(x)`. At `t = 0` this is
`V*_0 = max_{{(C_t,μ_t)}} −(1/k) ln E[exp(−k(Σ_t β^t U_t(C_t) + β^N h))] = −(1/k) ln E^{φ*}[…]`.

**Formalization Note** The comparison class is all deterministic plans depending on the realized
disaster history, admissible along every history. -/
theorem eq_A_10_verification {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (M : Model S) (hM : M.Standing) (V : ℕ → State S → ℝ) (φ : ℕ → State S → ℝ × ℝ)
    (hterm : ∀ x : State S, M.InBox x → V M.N x = M.h x.1 x.2.1 x.2.2)
    (hbell : ∀ t < M.N, ∀ x : State S, M.InBox x →
      IsGreatest {r | ∃ a, AdmissibleAction x a ∧ r = M.obj t (V (t + 1)) x a} (V t x))
    (hφ : ∀ t < M.N, ∀ x : State S, M.InBox x →
      AdmissibleAction x (φ t x) ∧ M.obj t (V (t + 1)) x (φ t x) = V t x) :
    ∀ t ≤ M.N, ∀ x : State S, M.InBox x →
      M.PlanAdmissible t x (M.markovPlan t x φ) ∧
      M.fullPathUtility t x (M.markovPlan t x φ) = V t x ∧
      ∀ π : Plan S, M.PlanAdmissible t x π → M.fullPathUtility t x π ≤ V t x := by sorry

end FullPathSCC
