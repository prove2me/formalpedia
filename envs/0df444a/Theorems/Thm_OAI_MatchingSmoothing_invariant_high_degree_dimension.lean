-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_invariant_high_degree_dimension
-- name    : OAI.MatchingSmoothing.invariant_high_degree_dimension
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:33:49.607779+00:00
-- url     : https://prove2.me/theorems/10ecac04-af12-44d6-a7ab-27378e2ef4ac
-- title:
--   Permutation-invariant spaces of functions on perfect matchings with no low-degree part have dimension at least $\binom{h}{k}$
-- statement:
--   Fix $h\in\mathbb N$ and let $V_h=\{0,\dots,h-1\}\times\{0,1\}$ be a set of $2h$ vertices. Let $\mathcal P_h$ be the set of perfect matchings of $V_h$, viewed as fixed-point-free involutions $M$ of $V_h$. The group $\mathrm{Sym}(V_h)$ acts on functions $F:\mathcal P_h\to\mathbb R$ by $(p\cdot F)(M)=F(p^{-1}Mp)$. For an ordered pair $(u,v)$ of vertices, let $x_{uv}:\mathcal P_h\to\{0,1\}$ be the edge indicator: $x_{uv}(M)=1$ if $M(u)=v$ and $0$ otherwise. Let $\mathcal L_d\subseteq\mathbb R^{\mathcal P_h}$ be the span of all products of at most $d$ edge indicators, the constant function $1$ included. These are the functions of degree at most $d$ in the edges.
--
--   Let $k\in\mathbb N$ with $4k<h$. Let $W\subseteq\mathbb R^{\mathcal P_h}$ be a nonzero subspace that is invariant under $\mathrm{Sym}(V_h)$ and meets the low-degree space trivially:
--
--   $$
--   W\cap\mathcal L_{(4k)^2}=\{0\}.
--   $$
--
--   Then
--
--   $$
--   \dim_{\mathbb R}W\ \ge\ \binom{h}{k}.
--   $$
--
--   So a permutation-invariant space of functions of perfect matchings that contains no nonzero function of degree at most $16k^2$ must be large. For instance, an eigenspace of an operator commuting with the $\mathrm{Sym}(V_h)$-action is an invariant subspace, so the theorem gives lower bounds on eigenvalue multiplicities. Such multiplicity bounds, combined with a bound on the trace of the square of the operator, control its largest eigenvalue.
--
--   **Formalization Note** In Lean the hypotheses are `4 * k < h`, invariance of `W` under every `Pairing.act p`, `Disjoint W (lowDegree Pairing.edgeCoord ((4 * k) * (4 * k)))`, and the existence of a nonzero element of `W`. The conclusion is `h.choose k ≤ Module.finrank ℝ W`. Edge indicators are indexed by all ordered pairs of vertices; those with $u=v$ are identically $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/RepresentationDimension.lean#L195-L250

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension

open OAI OAI.MatchingSmoothing
universe u_1
variable {h : ℕ}

theorem OAI.MatchingSmoothing.invariant_high_degree_dimension (k : ℕ) (hk : 4 * k < h)
    (W : Submodule ℝ (Pairing (Vertices h) → ℝ))
    (hW : ∀ p f, f ∈ W → Pairing.act p f ∈ W)
    (hdis : Disjoint W (lowDegree Pairing.edgeCoord ((4 * k) * (4 * k))))
    (hne : ∃ f ∈ W, f ≠ 0) : h.choose k ≤ Module.finrank ℝ W := by sorry
