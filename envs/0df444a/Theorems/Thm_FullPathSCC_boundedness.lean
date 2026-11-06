-- Prove2me | Theorems.Thm_FullPathSCC_boundedness
-- name    : FullPathSCC.boundedness
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:14.711195+00:00
-- url     : https://prove2.me/theorems/01b461c7-8b76-4249-b380-832d55ef6323
-- title:
--   (A.8) and proof of Theorem A.2, p.7602 — the solution of the Bellman equation is bounded
-- statement:
--   Let $\bar K,\bar T,k>0$, $0<\beta<1$ and $N\in\mathbb N$, let $\mathcal S$ be a finite nonempty set of disaster states, and let the data $p$, $U_t$, $g_{K,t}$, $g_{T,t}$, $h$ satisfy the standing assumptions of §3.1 (see the definition `FullPathSCC.Model`). States are $x=(K,T,\vartheta)$ in the box $[0,\bar K]\times[0,\bar T]\times\mathcal S$; an action $(C,\mu)$ is admissible at $x$ when $0\le C\le K$ and $0\le\mu\le1$; $k_t=k\beta^t$. Let $V_0,\dots,V_N$ satisfy $V_N=h$ on the box and the Bellman equation (8) with attained maximum at every state of the box for $t<N$. Then
--
--   1. (A.8) there is $M$ with $|U_t(C)|\le M$ for all $t<N$, $C\in[0,\bar K]$, and $|h|\le M$ on the box;
--   2. for every such $M$, every $t\le N$ and every $x$ in the box,
--
--   $$
--   |V_t(x)|\le M\sum_{s=0}^{N-t}\beta^s .
--   $$
--
--   This is the boundedness of $V^*_t$, $0\le t\le N$, which the paper derives from the boundedness of $U_t$ and $h$.
--
--   Differences from the source:
--   - reading: (A.8): the maximum over $0\le t\le N$ and $C_t\in[0,K_t]$ → a bound over $t<N$ and $C\in[0,\bar K]$; reason: $U_t$ is given for $t=0,\dots,N-1$ (§3.1), and $K_t$ ranges over $[0,\bar K]$
--   - generalization: $V^*_t$ is bounded → the explicit bound $|V_t(x)|\le M\sum_{s=0}^{N-t}\beta^s$ for every $M$ bounding $|U_t|$ and $|h|$; reason: an explicit bound implies boundedness
--   - generalization: the solution $V^*$ of (A.9) → any $V$ with $V_N=h$ and (8) with attained maximum; reason: $V^*$ is such a $V$
--   - reading: $K_t\in[0,\bar K]$, $T_t\in[0,\bar T]$ at every $t$ (§3.1), while $g_{K,t}:D_{K,t}\to\mathbb R$ and $g_{T,t}:D_{T,t}\to\mathbb R$ → $g_{K,t}$ maps $D_{K,t}$ into $[0,\bar K]$ and $g_{T,t}$ maps $D_{T,t}$ into $[0,\bar T]$ for $t<N$; reason: (8) evaluates $V_{t+1}$, and $V_N\equiv h$ given on $[0,\bar K]$, at $(g_{K,t},g_{T,t},j)$, so the next state must lie in the box where they are defined
--   - generalization: $g_{K,t}$, $g_{T,t}$, $p_{\vartheta,\hat\vartheta}$, $U_t$, $h$ of class $C^1$ → continuous on the same domains; reason: $C^1$ functions are continuous, so every model of §3.1 satisfies the hypotheses
--   - generalization: $U_t$ strictly increasing, with values in $\mathbb R_+$, and $U_t(0)=0$ → no monotonicity, sign or normalization condition on $U_t$; reason: dropped hypotheses: every utility of §3.1 is allowed
--   - generalization: $\mathcal S=\{1,2,3,4\}$ → any finite nonempty set of disaster states; reason: $\{1,2,3,4\}$ is an instance
--   - generalization: $h:[0,\bar K]\to\mathbb R$ of class $C^1$ → $h$ continuous in $(K,T)$ on $[0,\bar K]\times[0,\bar T]$ for each disaster state; reason: the paper's $h$ is the instance $h(K,T,\vartheta)=h(K)$
--   - encoding: $p_{\vartheta,\hat\vartheta}:[0,\bar T]\to[0,1]$ is the transition probability from $\vartheta$ to $\hat\vartheta$ → $p\ge0$ and $\sum_{\hat\vartheta}p_{\vartheta,\hat\vartheta}(T)=1$ for $T\in[0,\bar T]$; reason: what a transition probability is; $p\le1$ follows
--   - encoding: $U_t\in C^1([0,K_t])$ for the current capital $K_t$ → $U_t$ continuous on $[0,\bar K]$; reason: $K_t$ ranges over $[0,\bar K]$, so $U_t$ is needed on all of $[0,\bar K]$; continuity there is continuity on every $[0,K_t]$
--   - generalization: $\infty>N\ge1$ (proof of Theorem A.2, p.7601) → $N\ge0$; reason: $N=0$ only adds a trivial case
-- source:
--   Zhao, Basu, Lontzek & Schmedders, The Social Cost of Carbon When We Wish for Full-Path Robustness, Management Science 69(12) (2023), doi:10.1287/mnsc.2023.4736, proof of Theorem A.2, (A.8), p.7601, and p.7602, "The boundedness of V*_t, 0 ≤ t ≤ N is obvious from the boundedness of U_t(·) and h(·)"

import Mathlib
import Definitions.Def_FullPathSCC_Model
import Definitions.Def_FullPathSCC_Model_obj
import Definitions.Def_FullPathSCC_Model_fullPathUtility

namespace FullPathSCC

open Model

/-- **(A.8) and "The boundedness of V*_t, 0 ≤ t ≤ N is obvious from the boundedness of U_t(·) and
h(·)"**, proof of Theorem A.2 (Management Science 69(12) (2023), pp.7601–7602). Let `V` solve the
Bellman equation (8) on the box with `V_N = h` and the maximum attained. Then

1. (A.8) there is `M` with `|U_t(C)| ≤ M` for `t < N`, `C ∈ [0, K̄]`, and `|h| ≤ M` on the box;
2. for every such bound `M`, every `t ≤ N` and every state `x` in the box,
   `|V_t(x)| ≤ M Σ_{s=0}^{N−t} β^s`. -/
theorem boundedness {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (M : Model S) (hM : M.Standing) (V : ℕ → State S → ℝ)
    (hterm : ∀ x : State S, M.InBox x → V M.N x = M.h x.1 x.2.1 x.2.2)
    (hbell : ∀ t < M.N, ∀ x : State S, M.InBox x →
      IsGreatest {r | ∃ a, AdmissibleAction x a ∧ r = M.obj t (V (t + 1)) x a} (V t x)) :
    (∃ B : ℝ, (∀ t < M.N, ∀ C ∈ Set.Icc 0 M.Kbar, |M.U t C| ≤ B) ∧
      ∀ x : State S, M.InBox x → |M.h x.1 x.2.1 x.2.2| ≤ B) ∧
    ∀ B : ℝ, (∀ t < M.N, ∀ C ∈ Set.Icc 0 M.Kbar, |M.U t C| ≤ B) →
      (∀ x : State S, M.InBox x → |M.h x.1 x.2.1 x.2.2| ≤ B) →
      ∀ t ≤ M.N, ∀ x : State S, M.InBox x →
        |V t x| ≤ B * ∑ s ∈ Finset.range (M.N - t + 1), M.β ^ s := by sorry

end FullPathSCC
