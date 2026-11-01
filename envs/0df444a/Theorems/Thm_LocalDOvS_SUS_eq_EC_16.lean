-- Prove2me | Theorems.Thm_LocalDOvS_SUS_eq_EC_16
-- name    : LocalDOvS.SUS.eq_EC_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:30:22.826506+00:00
-- url     : https://prove2.me/theorems/468297be-ff13-41be-9104-808fb9f9921d
-- title:
--   Induction and (EC.16), pp.ec15–ec17 (corrected: on the good event, for the corrected algorithm)
-- statement:
--   Let $N\ge2$, $\sigma>0$, $\epsilon>0$, $\delta\in(0,1]$, let $f$ be discretely convex on $[N]$, and let $\omega$ be a tape in the good event $G$ for $f$. Run the corrected SUS algorithm on $\omega$ with any rules for the Type-I pair and the final tie. Then at every time $t$, for the iteration $k$ in progress:
--
--   1. $\displaystyle\min_{x\in S_k}f(x)\le\min_{x\in X}f(x)+\frac\epsilon2$;
--   2. $\{x_{L,k},\dots,x_{U,k}\}\subseteq[N]$ and $\displaystyle\min_{x\in\{x_{L,k},\dots,x_{U,k}\}}f(x)=\min_{x\in X}f(x)$;
--
--   and if the algorithm stops at time $t$ and returns $z$, then $z\in[N]$ and
--
--   $$
--   f(z)\le\min_{x\in X}f(x)+\epsilon .
--   $$
--
--   Event 1 at the last iteration is (EC.16). Together with the bound on $P(G^c)$ this gives the $(\epsilon,\delta)$-PGS guarantee of Theorem 2.
--
--   Differences from the source:
--   - correction: the two events happen jointly with probability at least 1 − (k − 1)δ/T_max, for the printed Algorithm 2 → the two events hold surely on the good event G, for the corrected algorithm (one test per active-set size); reason: the per-iteration union bound is over data-selected pairs and the printed algorithm is not PGS (N = 3, Gaussian noise, f = (0, 2ε, 4ε), small ε); P(Gᶜ) is bounded once (good_event)
--   - correction: the sub-problem returns an (ϵ/2, δ/T_max)-PGS point → on G the returned point is ε-optimal; reason: the same argument on the event G, where the final half-widths are at most ε/4
--   - generalization: f the objective of a model in M_C and the random simulation outputs → any discretely convex f and any tape in G(f); reason: specializes to the model's objective and tape
--   - generalization: x, y ∈ S such that … (some pair) → every pick and tie rule; reason: contains every choice
--   - encoding: min_{x∈{x_L,…,x_U}} f(x) = min_{x∈X} f(x) → {x_L, …, x_U} ⊆ [N] and it contains a global minimizer; reason: the same statement for an interval inside [N]
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, proof of Theorem 2, pp.ec15 and ec17, eq. (EC.16)

import Mathlib
import Definitions.Def_LocalDOvS_SUS_sus
import Definitions.Def_LocalDOvS_SUS_susState__311ba0
import Definitions.Def_LocalDOvS_SUS_histAt
import Definitions.Def_LocalDOvS_SUS_GoodEvent
import Definitions.Def_LocalDOvS_SUS_DiscConvex

open scoped NNReal

namespace LocalDOvS.SUS

/-- **The induction of the proof of Theorem 2 and (EC.16), pp.ec15 and ec17**
(Zhang–Zheng–Lavaei, arXiv:2012.02427v2), corrected. Let `f` be convex on `[N]` and let `ω` be
a tape in the good event `G` for `f`. Then along the run of the corrected shrinking uniform
sampling algorithm on `ω`, for every pick and tie rule, at every time `t` the two events of the
induction hold for the state `(S_k, x_{L,k}, x_{U,k})` of the iteration in progress:

1. `min_{x ∈ S_k} f(x) ≤ min_{x ∈ X} f(x) + ε/2`;
2. `min_{x ∈ {x_{L,k}, …, x_{U,k}}} f(x) = min_{x ∈ X} f(x)` (with `{x_{L,k}, …, x_{U,k}} ⊆ [N]`);

and if the algorithm stops at time `t` and returns `z`, then `z ∈ [N]` and
`f(z) ≤ min_{x ∈ X} f(x) + ε`.

**Formalization Note (correction).** The paper proves the two events "jointly with probability
at least `1 − (k − 1)δ/T_max`" by a per-iteration union bound over data-selected pairs; here
they hold surely on `G`, whose probability is bounded separately (`good_event`). Event 2 is
written "`[x_L, x_U] ⊆ [N]` and it contains a global minimizer", which is the printed equality.
Event 1 at the last iteration is (EC.16). -/
theorem eq_EC_16 (N : ℕ) (hN : 2 ≤ N) (σ : ℝ≥0) (hσ : 0 < σ) (ε : ℝ) (hε : 0 < ε)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (f : ℕ → ℝ) (hf : DiscConvex N f)
    (pick : SUSState → (ℕ → ℕ → ℝ) → ℕ × ℕ) (tie : SUSState → (ℕ → ℕ → ℝ) → Bool)
    (ω : ℕ × ℕ → ℝ) (hω : ω ∈ GoodEvent N σ ε δ f) (t : ℕ) :
    let A := sus N σ ε δ pick tie
    let st := susState N σ ε δ pick tie (histAt A ω t)
    ((∃ x ∈ actSet st, ∀ y ∈ Finset.Icc 1 N, f x ≤ f y + ε / 2) ∧
      (1 ≤ st.xL ∧ st.xU ≤ N ∧ ∃ x ∈ Finset.Icc st.xL st.xU, ∀ y ∈ Finset.Icc 1 N, f x ≤ f y)) ∧
    ∀ z, A (histAt A ω t) = Step.stop z →
      z ∈ Finset.Icc 1 N ∧ ∀ y ∈ Finset.Icc 1 N, f z ≤ f y + ε := by sorry

end LocalDOvS.SUS
