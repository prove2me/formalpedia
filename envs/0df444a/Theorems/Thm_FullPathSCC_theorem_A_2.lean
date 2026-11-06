-- Prove2me | Theorems.Thm_FullPathSCC_theorem_A_2
-- name    : FullPathSCC.theorem_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:17.474287+00:00
-- url     : https://prove2.me/theorems/879ac428-9e42-4dee-9160-b36e9db1d882
-- title:
--   Theorem A.2 — the risk-sensitive Bellman equation (8) has a bounded solution and an optimal deterministic Markov policy $\varphi^*_t=\varphi^*(k\beta^t,\cdot)$
-- statement:
--   Let $\bar K,\bar T,k>0$, $0<\beta<1$ and $N\in\mathbb N$, let $\mathcal S$ be a finite nonempty set of disaster states, and let the data $p$, $U_t$, $g_{K,t}$, $g_{T,t}$, $h$ satisfy the standing assumptions of §3.1 (see the definition `FullPathSCC.Model`). States are $x=(K,T,\vartheta)$ in the box $[0,\bar K]\times[0,\bar T]\times\mathcal S$; an action $(C,\mu)$ is admissible at $x$ when $0\le C\le K$ and $0\le\mu\le1$; $k_t=k\beta^t$. Then there exist functions $V^*_0,\dots,V^*_N$ on states and a deterministic (nonstationary) Markov policy $\varphi^*_t(K,T,\vartheta)$ such that:
--
--   1. $V^*_N=h$ on the box;
--   2. for every $t<N$ and $x=(K,T,\vartheta)$ in the box, $V^*_t$ solves the Bellman equation (8) with the maximum attained:
--   $$
--   V^*_t(x)=\max_{(C,\mu)\in[0,K]\times[0,1]}\Bigl[U_t(C)-\frac1{k_t}\ln\Bigl(\sum_{j\in\mathcal S}p_{\vartheta j}(T)\exp\bigl(-k_t\beta V^*_{t+1}(g_{K,t}(K,T,\vartheta,C,\mu),g_{T,t}(K,T,\mu),j)\bigr)\Bigr)\Bigr];
--   $$
--   3. the $V^*_t$, $t\le N$, are bounded on the box by a common constant;
--   4. (A.4) for $t<N$, $\varphi^*_t(x)$ is admissible and attains the maximum in (8);
--   5. (A.5) and optimality: for every $t\le N$ and $x$ in the box, the plan induced by $\varphi^*$ from $(t,x)$ is admissible, its full-path utility equals $V^*_t(x)$,
--   $$
--   V^*_t(x)=-\frac1{k\beta^t}\ln E^{\varphi^*}\Bigl[\exp\Bigl(-k\beta^t\Bigl(\sum_{n=0}^{N-t-1}\beta^nU_{t+n}(C_n)+\beta^{N-t}h(X_{N-t})\Bigr)\Bigr)\Bigm|X_0=x\Bigr],
--   $$
--   and every plan admissible from $(t,x)$ has full-path utility at most $V^*_t(x)$;
--   6. there is a function $\varphi^*$ with $\varphi^*_t(x)=\varphi^*(k\beta^t,x)$ for all $t<N$ and $x$ in the box.
--
--   This is the existence result that justifies solving (8) numerically for the social cost of carbon under full-path robust preferences: the Bellman solution is the optimal full-path utility, attained by a Markov policy that depends on time only through $k_t$, so the policy is subpath optimal (time consistent).
--
--   Differences from the source:
--   - generalization: (A.5) at $t=0$, "maximizing" and "subpath optimal" → for every $t\le N$ and $x$ in the box: $J_t^{\varphi^*}(x)=V^*_t(x)$ and $J_t^\pi(x)\le V^*_t(x)$ for every admissible plan; reason: $t=0$ gives (A.5) and the maximum of (A.10)
--   - generalization: the maximum over control sequences $\{(C_t,\mu_t)\}_{0\le t\le N-1}$ in (A.10), and Markov policies → every deterministic plan whose actions depend on the realized disaster history; reason: Markov policies are such plans; the bound $J\le V$ holds for the larger class
--   - reading: $\beta^N h(C_N)$ in (A.5), (A.10), (A.11) → $\beta^{N-t}h$ at the terminal state $X_N=(K_N,T_N,\vartheta_N)$; reason: no control $C_N$ exists (controls run over $t\le N-1$) and $V_N\equiv h$ is the terminal value
--   - encoding: $\varphi^*:[k\beta^N,k]\times\mathbb R_+\times\mathbb R_+\times\mathcal S\to\mathbb R_+\times[0,1]$ → $\Phi:\mathbb R\times(\text{states})\to\mathbb R\times\mathbb R$ with $\varphi^*_t(x)=\Phi(k\beta^t,x)$ for $t<N$, $x$ in the box; reason: only the values at $k\beta^t\in[k\beta^N,k]$ are constrained, and $\varphi^*_t(x)$ is admissible, so it lies in $\mathbb R_+\times[0,1]$
--   - encoding: a "Markov policy" (a measurable decision rule in the framework of Bäuerle and Rieder (2014), though neither Theorem A.2 nor (A.9) says measurable, and the paper writes "for some function") → $\varphi$ an arbitrary function of $(t,K,T,\vartheta)$; reason: from a fixed start state only finitely many states are reached along the finite chain, so no quantity of the statement depends on the measurability of $\varphi$
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
--   Zhao, Basu, Lontzek & Schmedders, The Social Cost of Carbon When We Wish for Full-Path Robustness, Management Science 69(12) (2023), doi:10.1287/mnsc.2023.4736, Theorem A.2, pp.7600–7601, with (A.4) and (A.5)

import Mathlib
import Definitions.Def_FullPathSCC_Model
import Definitions.Def_FullPathSCC_Model_obj
import Definitions.Def_FullPathSCC_Model_fullPathUtility

namespace FullPathSCC

open Model

/-- **Theorem A.2** (Management Science 69(12) (2023), pp.7600–7601). Under the assumptions of
§3.1, the Bellman equation (8) has a bounded solution `V*_t`, `0 ≤ t ≤ N`, `V*_N = h`, with the
maximum attained at every state, and a maximizing (nonstationary) deterministic Markov policy
`φ*_t` with `φ*_t(K, T, ϑ) ∈ argmax` of (A.4), such that `V*_t` is the full-path utility (A.5) of
`φ*` and the maximum of the full-path utility over all admissible plans, from every time
`t ≤ N` and every state (subpath optimality), and `φ*_t(·) = φ*(k_t, ·)` with `k_t = kβ^t`.

**Formalization Note** States are triples `(K, T, ϑ)` in the box `[0, K̄] × [0, T̄] × 𝒮`; actions
are pairs `(C, μ)` with `C ∈ [0, K]`, `μ ∈ [0, 1]`. Plans may depend on the realized disaster
history. The full-path utility is the explicit sum over disaster paths. -/
theorem theorem_A_2 {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (M : Model S) (hM : M.Standing) :
    ∃ (V : ℕ → State S → ℝ) (φ : ℕ → State S → ℝ × ℝ),
      (∀ x : State S, M.InBox x → V M.N x = M.h x.1 x.2.1 x.2.2) ∧
      (∀ t < M.N, ∀ x : State S, M.InBox x →
        IsGreatest {r | ∃ a, AdmissibleAction x a ∧ r = M.obj t (V (t + 1)) x a} (V t x)) ∧
      (∃ B : ℝ, ∀ t ≤ M.N, ∀ x : State S, M.InBox x → |V t x| ≤ B) ∧
      (∀ t < M.N, ∀ x : State S, M.InBox x →
        AdmissibleAction x (φ t x) ∧ M.obj t (V (t + 1)) x (φ t x) = V t x) ∧
      (∀ t ≤ M.N, ∀ x : State S, M.InBox x →
        M.PlanAdmissible t x (M.markovPlan t x φ) ∧
        M.fullPathUtility t x (M.markovPlan t x φ) = V t x ∧
        ∀ π : Plan S, M.PlanAdmissible t x π → M.fullPathUtility t x π ≤ V t x) ∧
      (∃ Φ : ℝ → State S → ℝ × ℝ, ∀ t < M.N, ∀ x : State S, M.InBox x →
        φ t x = Φ (M.k * M.β ^ t) x) := by sorry

end FullPathSCC
