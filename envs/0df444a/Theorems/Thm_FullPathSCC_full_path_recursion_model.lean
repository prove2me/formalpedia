-- Prove2me | Theorems.Thm_FullPathSCC_full_path_recursion_model
-- name    : FullPathSCC.full_path_recursion_model
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:11.033233+00:00
-- url     : https://prove2.me/theorems/150b447d-d805-45d2-8535-fbcb6c812f40
-- title:
--   (6) with $E_t=\mathbb E^{(C_t,\mu_t)}$, p.7591 — in the model of §3.1 the full-path utility of a plan satisfies the one-step recursion (the model instance of Proposition A.1)
-- statement:
--   Let $\bar K,\bar T,k>0$, $0<\beta<1$ and $N\in\mathbb N$, let $\mathcal S$ be a finite nonempty set of disaster states, and let the data $p$, $U_t$, $g_{K,t}$, $g_{T,t}$, $h$ satisfy the standing assumptions of §3.1 (see the definition `FullPathSCC.Model`). States are $x=(K,T,\vartheta)$ in the box $[0,\bar K]\times[0,\bar T]\times\mathcal S$; an action $(C,\mu)$ is admissible at $x$ when $0\le C\le K$ and $0\le\mu\le1$; $k_t=k\beta^t$. Let $0\le t<N$, $x=(K,T,\vartheta)$ in the box, and $\pi$ a plan admissible from $(t,x)$ whose first action is $(C,\mu)$. For $j\in\mathcal S$ let $x'_j=(g_{K,t}(K,T,\vartheta,C,\mu),g_{T,t}(K,T,\mu),j)$ and let $\pi_j$ be the continuation of $\pi$ after the first transition to $j$. Then
--
--   $$
--   J_t^\pi(x)=U_t(C)-\frac1{k_t}\ln\Bigl(\sum_{j\in\mathcal S}p_{\vartheta j}(T)\exp\bigl(-k_t\beta\,J_{t+1}^{\pi_j}(x'_j)\bigr)\Bigr),
--   $$
--
--   which is $V_t=u(c_t)+\mathcal E^{FP}_t(\beta V_{t+1})$ with $\mathcal E^{FP}_t(\cdot)=-\frac1{k\beta^t}\ln E_t[e^{-k\beta^t(\cdot)}]$.
--
--   This is Proposition A.1 for the process of §3.1, which the paper uses to pass from (6) to the Bellman equation (8). The general statement is `FullPathSCC.prop_A_1`.
--
--   Differences from the source:
--   - reading: (6) with $\sum_{s=t}^N\beta^{s-t}u(c_s)$, a utility at time $N$ → the last summand is the terminal value $\beta^{N-t}h(X_N)$ of (A.5); reason: in §3.1 controls run over $t\le N-1$ and $V_N\equiv h$
--   - reading: $t\ge0$ → $0\le t<N$; reason: $V_{t+1}$ exists only for $t+1\le N$
--   - encoding: the conditional expectation $E_t$ in $\mathcal E^{FP}_t(\beta V_{t+1})$ → the transition sum (7) over the next disaster state $j$, with the continuation plan's full-path utility from $x'_j$; reason: finite chain; same value
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
--   Zhao, Basu, Lontzek & Schmedders, The Social Cost of Carbon When We Wish for Full-Path Robustness, Management Science 69(12) (2023), doi:10.1287/mnsc.2023.4736, §3.1, p.7591, "using Equation (6) and putting $E_t[\cdot]=\mathbb E^{(C_t,\mu_t)}[\cdot|K_t,T_t,\vartheta_t]$ therein"; Proposition A.1, (A.1) and (A.2), p.7600

import Mathlib
import Definitions.Def_FullPathSCC_Model
import Definitions.Def_FullPathSCC_Model_obj
import Definitions.Def_FullPathSCC_Model_fullPathUtility

namespace FullPathSCC

open Model

/-- **Equation (6) in the model of §3.1** (Management Science 69(12) (2023), p.7591: "using
Equation (6) and putting `E_t[·] = 𝔼^{(C_t,μ_t)}[·|K_t, T_t, ϑ_t]` therein"): the instance of
Proposition A.1 (`prop_A_1`) behind the Bellman equation (8). For `t < N`, a state
`x = (K, T, ϑ)` in the box and a plan `π` admissible from `(t, x)` with first action
`(C, μ) = π 0 ()`,
`J_t^π(x) = U_t(C) − (1/k_t) ln Σ_{j∈𝒮} p_{ϑ j}(T) exp(−k_t β J_{t+1}^{π_j}(x'_j))`,
where `x'_j = (g_{K,t}(K,T,ϑ,C,μ), g_{T,t}(K,T,μ), j)` and `π_j` is the continuation of `π` after
the first transition to `j`.

**Formalization Note** The conditional expectation `E_t` of (6) is the transition sum (7); the
last summand of (6) is the terminal value `β^{N−t} h(X_N)` of (A.5). Both sides are computed from
the explicit path sum `fullPathUtility`. -/
theorem full_path_recursion_model {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S] (M : Model S)
    (hM : M.Standing) (t : ℕ) (ht : t < M.N) (x : State S) (hx : M.InBox x) (π : Plan S)
    (hπ : M.PlanAdmissible t x π) :
    M.fullPathUtility t x π =
      M.U t (π 0 Fin.elim0).1 - 1 / M.kt t * Real.log (∑ j : S, M.p x.2.2 j x.2.1 *
        Real.exp (-(M.kt t) * M.β *
          M.fullPathUtility (t + 1) (M.next t x (π 0 Fin.elim0) j) (shiftPlan π j))) := by sorry

end FullPathSCC
