-- Prove2me | Theorems.Thm_FullPathSCC_eq_A_9_bellman_solution
-- name    : FullPathSCC.eq_A_9_bellman_solution
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:15.476197+00:00
-- url     : https://prove2.me/theorems/17e11947-6c51-4b1c-965a-d163938f5d2f
-- title:
--   (A.9), proof of Theorem A.2 — the dynamic programming equation has a bounded (continuous) solution with a maximizing Markov policy
-- statement:
--   Let $\bar K,\bar T,k>0$, $0<\beta<1$ and $N\in\mathbb N$, let $\mathcal S$ be a finite nonempty set of disaster states, and let the data $p$, $U_t$, $g_{K,t}$, $g_{T,t}$, $h$ satisfy the standing assumptions of §3.1 (see the definition `FullPathSCC.Model`). States are $x=(K,T,\vartheta)$ in the box $[0,\bar K]\times[0,\bar T]\times\mathcal S$; an action $(C,\mu)$ is admissible at $x$ when $0\le C\le K$ and $0\le\mu\le1$; $k_t=k\beta^t$. Then there are functions $V^*_0,\dots,V^*_N$ on states and a deterministic (nonstationary) Markov policy $\varphi^*_t(K,T,\vartheta)$ such that:
--
--   1. $V^*_N=h$ on the box;
--   2. for every $t\le N$ and $\vartheta$, $(K,T)\mapsto V^*_t(K,T,\vartheta)$ is continuous on $[0,\bar K]\times[0,\bar T]$;
--   3. for every $t<N$ and $x=(K,T,\vartheta)$ in the box,
--   $$
--   V^*_t(x)=\max_{(C,\mu)\in[0,K]\times[0,1]}\Bigl[U_t(C)-\frac1{k_t}\ln\Bigl(\sum_{j\in\mathcal S}p_{\vartheta j}(T)\exp\bigl(-k_t\beta\,V^*_{t+1}(g_{K,t}(K,T,\vartheta,C,\mu),g_{T,t}(K,T,\mu),j)\bigr)\Bigr)\Bigr],
--   $$
--   the maximum being attained;
--   4. the $V^*_t$, $t\le N$, are bounded on the box by a common constant;
--   5. for $t<N$, $\varphi^*_t(x)$ is an admissible action attaining this maximum ($\varphi^*_t(x)\in\operatorname{argmax}$, as in (A.9)).
--
--   This is the backward induction that the paper obtains from Bäuerle and Rieder (2014).
--
--   Differences from the source:
--   - generalization: a bounded solution $V^*_t$ → a bounded solution with each $V^*_t$ continuous in $(K,T)$ on the box for each disaster state; reason: a stronger conclusion; it contains the claim of the page, and the backward induction carries this continuity
--   - encoding: the first form of (A.9) on the extended state $(t',k_t\beta,K,T,\vartheta)$ with $\delta_{t+1,t'}$ → the second form of (A.9), on $(K,T,\vartheta)$ at fixed $t$; reason: (A.9) states that the two argmax sets are equal
--   - encoding: a "Markov policy" (a measurable decision rule in the framework of Bäuerle and Rieder (2014), though neither Theorem A.2 nor (A.9) says measurable, and the paper writes "for some function") → $\varphi$ an arbitrary function of $(t,K,T,\vartheta)$; reason: from a fixed start state only finitely many states are reached along the finite chain, so no quantity of the statement depends on the measurability of $\varphi$
--   - reading: $K_t\in[0,\bar K]$, $T_t\in[0,\bar T]$ at every $t$ (§3.1), while $g_{K,t}:D_{K,t}\to\mathbb R$ and $g_{T,t}:D_{T,t}\to\mathbb R$ → $g_{K,t}$ maps $D_{K,t}$ into $[0,\bar K]$ and $g_{T,t}$ maps $D_{T,t}$ into $[0,\bar T]$ for $t<N$; reason: (8) evaluates $V_{t+1}$, and $V_N\equiv h$ given on $[0,\bar K]$, at $(g_{K,t},g_{T,t},j)$, so the next state must lie in the box where they are defined
--   - generalization: $g_{K,t}$, $g_{T,t}$, $p_{\vartheta,\hat\vartheta}$, $U_t$, $h$ of class $C^1$ → continuous on the same domains; reason: $C^1$ functions are continuous, so every model of §3.1 satisfies the hypotheses
--   - generalization: $U_t$ strictly increasing, with values in $\mathbb R_+$, and $U_t(0)=0$ → no monotonicity, sign or normalization condition on $U_t$; reason: dropped hypotheses: every utility of §3.1 is allowed
--   - generalization: $\mathcal S=\{1,2,3,4\}$ → any finite nonempty set of disaster states; reason: $\{1,2,3,4\}$ is an instance
--   - generalization: $h:[0,\bar K]\to\mathbb R$ of class $C^1$ → $h$ continuous in $(K,T)$ on $[0,\bar K]\times[0,\bar T]$ for each disaster state; reason: the paper's $h$ is the instance $h(K,T,\vartheta)=h(K)$
--   - encoding: $p_{\vartheta,\hat\vartheta}:[0,\bar T]\to[0,1]$ is the transition probability from $\vartheta$ to $\hat\vartheta$ → $p\ge0$ and $\sum_{\hat\vartheta}p_{\vartheta,\hat\vartheta}(T)=1$ for $T\in[0,\bar T]$; reason: what a transition probability is; $p\le1$ follows
--   - encoding: $U_t\in C^1([0,K_t])$ for the current capital $K_t$ → $U_t$ continuous on $[0,\bar K]$; reason: $K_t$ ranges over $[0,\bar K]$, so $U_t$ is needed on all of $[0,\bar K]$; continuity there is continuity on every $[0,K_t]$
--   - generalization: $\infty>N\ge1$ (proof of Theorem A.2, p.7601) → $N\ge0$; reason: $N=0$ only adds a trivial case
-- source:
--   Zhao, Basu, Lontzek & Schmedders, The Social Cost of Carbon When We Wish for Full-Path Robustness, Management Science 69(12) (2023), doi:10.1287/mnsc.2023.4736, proof of Theorem A.2, (A.9), p.7601

import Mathlib
import Definitions.Def_FullPathSCC_Model
import Definitions.Def_FullPathSCC_Model_obj
import Definitions.Def_FullPathSCC_Model_fullPathUtility

namespace FullPathSCC

open Model

/-- **(A.9), proof of Theorem A.2** (Management Science 69(12) (2023), p.7601): "there indeed
exists a (bounded) solution `V*_t(·)`, `0 ≤ t ≤ N` to the dynamic programming equation … and a
corresponding deterministic maximizing (nonstationary) Markov policy". There are `V` and `φ` with
`V_N = h` on the box, each `V_t` continuous on `[0, K̄] × [0, T̄]` in `(K, T)` for each disaster
state, `V_t` solving (8) on the box with the maximum attained, the `V_t` bounded on the box by a
common constant, and `φ_t(x)` an admissible action attaining the maximum (`φ_t(x) ∈ argmax`, as in
(A.9)).

**Formalization Note** The paper obtains this from corollary 2 and remark 2 of Bäuerle and Rieder
(2014). The statement adds the continuity of `V_t`, which the backward induction carries. -/
theorem eq_A_9_bellman_solution {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (M : Model S) (hM : M.Standing) :
    ∃ (V : ℕ → State S → ℝ) (φ : ℕ → State S → ℝ × ℝ),
      (∀ x : State S, M.InBox x → V M.N x = M.h x.1 x.2.1 x.2.2) ∧
      (∀ t ≤ M.N, ∀ ϑ : S, ContinuousOn (fun z : ℝ × ℝ => V t (z.1, z.2, ϑ))
        (Set.Icc 0 M.Kbar ×ˢ Set.Icc 0 M.Tbar)) ∧
      (∀ t < M.N, ∀ x : State S, M.InBox x →
        IsGreatest {r | ∃ a, AdmissibleAction x a ∧ r = M.obj t (V (t + 1)) x a} (V t x)) ∧
      (∃ B : ℝ, ∀ t ≤ M.N, ∀ x : State S, M.InBox x → |V t x| ≤ B) ∧
      (∀ t < M.N, ∀ x : State S, M.InBox x →
        AdmissibleAction x (φ t x) ∧ M.obj t (V (t + 1)) x (φ t x) = V t x) := by sorry

end FullPathSCC
