-- Prove2me | Theorems.Thm_IncrementalER_lemma_5_6
-- name    : IncrementalER.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:09:06.983892+00:00
-- url     : https://prove2.me/theorems/ea6b103c-1553-4729-8d40-3c1a80cf31b0
-- title:
--   Lemma 5.6, p.35 — $\Pr_Q[u_{\tau_\square-1}=u\wedge A]=\frac{K_{vv}b_u}{a_v}p_u(\tau_v<\tau_{U\setminus\{v\}})$
-- statement:
--   Let $G$ be a connected graph, $\emptyset\neq S_0\subseteq U\subseteq V$, $v\in U\setminus S_0$, $K=L^{-1}_{\bar S_0,\bar S_0}$, $b>0$ on $\bar S_0$, $a=Kb$, and let $Q$ be the Doob-transformed chain and $A$ the event of p.35. Then for every $u\in V\setminus S_0$,
--
--   $$\Pr_Q\big[u_{\tau_\square-1}=u\wedge A\big]=\frac{K_{vv}b_u}{a_v}\,p_u(\tau_v<\tau_{U\setminus\{v\}}),$$
--
--   where for $u=v$ we interpret $p_v(\tau_v<\tau_{U\setminus\{v\}})=1$. Sampling the last state before absorption together with the indicator of $A$ thus gives an unbiased estimator of the leverage degree $\ell^G_U(v)$ via (19). Connectivity is the paper's standing assumption ("We assume throughout that everywhere we are dealing exclusively with connected graphs", p.10) and is a hypothesis.
--
--   Differences from the source:
--   - encoding: G = (V, E, c) an undirected capacitated multigraph (p.10) → a symmetric nonnegative conductance function with zero diagonal (parallel capacities added, no loops); reason: the Laplacian, effective resistances, leverage degrees and the random walk are unchanged by merging parallel edges; the paper's edges (u, v) join two vertices, and the source never uses loops
--   - generalization: b with ½ deg ≤ b ≤ 2 deg ((17), p.31) → any b positive on S̄0; reason: the lemma and its proof use only b > 0 and a = K b; the paper's b is positive
--   - encoding: S0 a nonempty k-hitting set (the setting of §5) → S0 nonempty; reason: the lemma's proof uses no hitting-set property; nonemptiness makes K defined
--   - encoding: Pr_Q[u_{τ□−1} = u ∧ A] for the chain started at v → the sum over t and trajectories v = u_0, …, u_t = u in S̄0 satisfying A of the path weight times Q(u, □); reason: these are exactly the trajectories with τ□ = t + 1, u_{τ□−1} = u and A
--   - encoding: for u = v we interpret p_v(τ_v < τ_{U\{v}}) = 1 → hitBefore c v v (U.erase v), which equals 1 by definition; reason: τ_v = 0 for the walk started at v
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 5.6, p.35; (17)–(18), p.31; chain Q, p.33; τ□, τ̄_v, A, p.35; connectivity, p.10

import Mathlib
import Definitions.Def_IncrementalER_doobChain
import Definitions.Def_IncrementalER_hitBefore

namespace IncrementalER

/-- **Lemma 5.6** (joint law of the last vertex before absorption and the event `A`).

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 5.6, p.35; the
vectors `a, b` of (17)–(18), p.31; the chain `Q`, p.33; `τ□`, `τ̄_v` and `A`, p.35; connectivity
assumption, p.10.

Let `G` be a connected graph, `∅ ≠ S0 ⊆ U ⊆ V`, `v ∈ U \ S0`, `K = L^{−1}_{S̄0,S̄0}`, `b > 0` on `S̄0`
and `a = K b`. For the chain `Q` started at `v`, for every `u ∈ V \ S0`,
`Pr_Q[u_{τ□−1} = u ∧ A] = (K_vv b_u / a_v) p_u(τ_v < τ_{U∖{v}})`, where `p_v(τ_v < τ_{U∖{v}}) = 1`.

**Formalization Note.** The paper's (17), `½ deg ≤ b ≤ 2 deg`, is not used by the lemma; any `b`
positive on `S̄0` is allowed (a generalization). `p_u(τ_v < τ_{U∖{v}})` is `hitBefore`, which is `1`
at `u = v` by definition of the hitting times, so the paper's interpretation needs no special
case. The left side is a sum over finite trajectories absorbed at time `τ□ = t + 1`. -/
theorem lemma_5_6 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (hc : IsGraph c)
    (hconn : Connected c) (S0 U : Finset V) (hS0 : S0.Nonempty) (hS0U : S0 ⊆ U)
    (v : V) (hvU : v ∈ U) (hvS0 : v ∉ S0) (b : V → ℝ) (hb : ∀ x, x ∉ S0 → 0 < b x)
    (u : V) (hu : u ∉ S0) :
    lastExitAProb c S0 b U v u =
      grounded c S0 ⟨v, hvS0⟩ ⟨v, hvS0⟩ * b u / doobA c S0 b v * hitBefore c u v (U.erase v) := by sorry

end IncrementalER
