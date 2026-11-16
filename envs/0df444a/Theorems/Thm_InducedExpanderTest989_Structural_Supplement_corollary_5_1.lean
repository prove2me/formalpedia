-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_Supplement_corollary_5_1
-- name    : InducedExpanderTest989.Structural.Supplement.corollary_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:31:18.757811+00:00
-- url     : https://prove2.me/theorems/45933d57-794e-46e8-bc5e-6841f606079a
-- title:
--   Corollary 5.1 — size slack implies small edit distance
-- statement:
--   Let $d\ge3$, $\alpha\in(0,1]$, $\kappa\in[3/4,1)$, $\beta=(1-\kappa)\alpha$ and $n\ge 4/((1-\kappa)\alpha)$. Write $\mathcal P_{\alpha,\phi}$ for the class of graphs on $[n]$ having a vertex set $U$ with $|U|\ge\alpha n$ and $\Phi_{\rm in}(G[U])\ge\phi$, with conductance normalized by $d$. For every $\theta\in(0,1]$ and every simple graph $G$ on $[n]$ of maximum degree at most $d$,
--   $$G\in\mathcal P_{\alpha-\beta,\theta}\ \Longrightarrow\ \mathrm{dist}_d\big(G,\mathcal P_{\alpha,\theta/(2d+2)}\big)\le\frac{5\beta}{2},$$
--   where $\mathrm{dist}_d(G,H)=|E(G)\triangle E(H)|/(dn)$ and the minimum ranges over graphs of maximum degree at most $d$.
--
--   The corollary converts a core that misses the size threshold by the slack $\beta n$ into a full-size core at small normalized edit distance. It is the soundness step of Theorem 5.1.
--
--   **Formalization Note** $\beta$ is the mission's `beta α κ`, and $n\ge4/\beta$ is `LargeEnough n α κ`. The conclusion is stated as the existence of a witness $H$ of maximum degree at most $d$ in $\mathcal P_{\alpha,\theta/(2d+2)}$ with $|E(G)\triangle E(H)|\le(5\beta/2)\,dn$.
--
--   Differences from the source:
--   - encoding: dist_d(G, P_{α,θ/(2d+2)}) ≤ 5β/2 → some H of maximum degree ≤ d with HasCore d H α (θ/(2d+2)) and |E(G)△E(H)| ≤ (5β/2)·d·n; reason: the minimum over the finite set of graphs on [n] is attained, and dn > 0
--   - encoding: G of maximum degree at most d (implicit) → hypothesis DegreeBound d G; reason: dist_d is defined only between graphs with degree bound d (§1.1)
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.33 (PDF p.35), Corollary 5.1; distance definition p.3 (PDF p.5)

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Parameters
import Definitions.Def_InducedExpanderTest989_Structural_Supplement_Distance

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural.Supplement

/-- Peng–Shen, STOC 2027 #989, Corollary 5.1 (p. 33, PDF 35), with `β = (1 − κ)α` = `beta α κ`.
`dist_d(G, P_{α,θ/(2d+2)}) ≤ 5β/2` is the existence of a target `H` of maximum degree at most
`d` with `|E(G) △ E(H)| ≤ (5β/2) d n`. -/
theorem corollary_5_1 (n d : ℕ) (α κ : ℝ) (hd : 3 ≤ d) (hα : 0 < α) (hα1 : α ≤ 1)
    (hκ : 3/4 ≤ κ) (hκ1 : κ < 1) (hn : LargeEnough n α κ) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (G : SimpleGraph (Fin n)) (hG : DegreeBound d G)
    (hcore : HasCore d G (α - beta α κ) θ) :
    ∃ H : SimpleGraph (Fin n), DegreeBound d H ∧ HasCore d H α (θ / (2 * d + 2)) ∧
      (editDistance G H : ℝ) ≤ (5 * beta α κ / 2) * d * n := by sorry

end InducedExpanderTest989.Structural.Supplement
