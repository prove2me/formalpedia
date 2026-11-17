-- Prove2me | Theorems.Thm_Max3CutHard_Supplement_theorem_4_1
-- name    : Max3CutHard.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:49:30.065199+00:00
-- url     : https://prove2.me/theorems/592ea692-1bd2-45b6-a472-3cc8d0d04e3a
-- title:
--   Theorem 4.1 — soundness criterion: $(\sum_tC_t/\bar w-\delta,\ \max_{x,y}S_y(x)/\bar w+\delta)$-hardness and ratio $\rho+\delta$
-- statement:
--   **Theorem 4.1 (Soundness criterion).** Let $k\ge3$ and let $(I_0,I_1,I_2)$ be a family of gadgets for Max-$k$-Cut with non-negative edge weights and no loops (every edge joins two distinct vertices), such that each gadget value $V_t(x,y)$ is symmetric under exchanging $x_2$ and $x_3$:
--
--   $$V_t(x_1,x_2,x_3,y)=V_t(x_1,x_3,x_2,y)\qquad\text{for all }t\in\mathbb Z_3,\ x\in[k]^3,\ y\in[k]^k.$$
--
--   Let $C_t$ be the completeness of $I_t$, $S_y(x)=\sum_tV_t(x,y)$, $\bar w=\sum_tw(I_t)$ and
--
--   $$\rho=\frac{\max_{x,y}S_y(x)}{\sum_{t\in\mathbb Z_3}C_t}.$$
--
--   1. If $\bar w>0$, then for every $\delta>0$ Max-$k$-Cut is $\Big(\dfrac{\sum_tC_t}{\bar w}-\delta,\ \dfrac{\max_{x,y}S_y(x)}{\bar w}+\delta\Big)$-hard.
--   2. If $\sum_tC_t>0$, then for every $\delta>0$ Max-$k$-Cut is NP-hard to approximate within $\rho+\delta$.
--
--   Here Max-$k$-Cut is $(c,s)$-hard if it is NP-hard to distinguish $\max_\chi\mathrm{cut}_\chi(G)\ge c\,w(G)$ from $\max_\chi\mathrm{cut}_\chi(G)\le s\,w(G)$.
--
--   The criterion turns the design of gadget reductions from Håstad's equations into a single optimisation over three gadgets; it yields Theorem 1.2 and is the object of the barrier Theorem 7.1.
--
--   Differences from the source:
--   - generalization: weighted graph G with non-negative real edge weights → ℕ-weighted loopless multigraph OptInapprox.MaxCut.WMaxCut (an edge listed m times has weight m) with the unary encoding encMaxCut; reason: the hard instances are a subclass of weighted graphs and the inclusion is polynomial-time, so hardness on the subclass implies the source's claim (same convention as the published goal theorem_1_1)
--   - encoding: the two cases of the gap problem → both promise sets also require 0 < w(G); reason: at w(G) = 0 both cases hold, so the problem is undefined there; the clause excludes only that case
--   - encoding: max over y ∈ Y_k (restricted growth strings) → max over all y : Fin k → Fin k; reason: the paper states (Section 2, p.5) that maxima of sums of gadget values over x and y ∈ Y_k equal those over all y ∈ [k]^k; same value
--   - encoding: the (c, s)-clause with c, s divided by w̄; ρ with denominator Σ_t C_t → the (c, s)-clause assumes 0 < w̄; the ρ-clause assumes 0 < Σ_t C_t; reason: the quotients are undefined at 0 (Lean would return 0); the hypotheses exclude only those cases
--   - reading: Max-k-Cut is NP-hard to approximate within r → ∃ c > 0, s with s/c ≤ r and MaxKCutHard k c s; reason: Section 2 defines (c, s)-hardness and states that it implies NP-hardness of approximation within s/c; the published goal uses the same reading
--   - encoding: symmetric under exchanging x2 and x3 → ∀ t x y, gval x y = gval (x ∘ Equiv.swap 1 2) y with 0-based primaries; reason: Lean convention; same condition
--   - encoding: a gadget is a weighted graph G = (V, E, w) with edges {u, v} (Section 2) → hypothesis hloop: every listed edge of every gadget joins two distinct vertices; reason: the published RGraph is a list of ordered pairs and admits loops, which are not edges of a graph in the paper's sense; the hypothesis restores the paper's notion and excludes no gadget the paper allows
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Theorem 4.1, p.7

import Mathlib
import Definitions.Def_Max3CutHard_MaxKCutHard
import Definitions.Def_Max3CutHard_IsNonneg
import Definitions.Def_Max3CutHard_Family
import Definitions.Def_Max3CutHard_Gadget_gval
import Definitions.Def_Max3CutHard_Ct
import Definitions.Def_Max3CutHard_Supplement_maxS
import Definitions.Def_Max3CutHard_Supplement_wbar
import Definitions.Def_Max3CutHard_Supplement_rho

namespace Max3CutHard.Supplement

open Max3CutHard

/-- **Theorem 4.1 (Soundness criterion).** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Theorem 4.1, p.7: "Let
`(I0, I1, I2)` be a family of gadgets for Max-k-Cut, `k ≥ 3`, such that each `V_t(x, y)` is
symmetric under exchanging `x2` and `x3`. Let `ρ = max_{y∈Y_k} max_{x∈[k]^3} S_y(x) / Σ_{t∈Z3} C_t`.
Then for every `δ > 0`, Max-k-Cut is NP-hard to approximate within `ρ + δ`. More precisely, with
`w̄ = Σ_t w(I_t)`, Max-k-Cut is `(Σ_t C_t / w̄ − δ, max_{x,y} S_y(x) / w̄ + δ)`-hard."

**Formalization Note.** Gadgets are the published `Gadget k` (any number of auxiliary vertices);
their weights are non-negative (`IsNonneg`) and every listed edge joins two distinct vertices
(`hloop`), as in Section 2's definition of a weighted graph `G = (V, E, w)` with edges `{u, v}`.
The published `RGraph` is a list of ordered pairs and admits loops, which are never cut but count
in `w̄`; without `hloop` the `(c, s)` clause is false (a large loop makes `maxS/w̄ + δ < 1 − 1/k`,
and no loopless graph has `max_χ cut_χ(G) < (1 − 1/k)·w(G)`). The
symmetry is on the values: `V_t(x, y) = V_t(x ∘ (1 2), y)` for every `t, x, y`, with 0-based
primaries (`x2, x3` are indices `1, 2`). `maxS` and `rho` maximise over all `y`, which equals
the paper's maximum over `y ∈ Y_k` (p.5). The `(c, s)` clause, which divides by `w̄`, carries
`0 < w̄`; the `ρ` clause, which divides by `Σ_t C_t`, carries `0 < Σ_t C_t`. "Approximate within
`r`" is read as in the published goal: `MaxKCutHard k c s` for some `c > 0`, `s/c ≤ r`.
Unconditional: Håstad's Theorem 2.1 is not a hypothesis. -/
theorem theorem_4_1 {k : ℕ} [NeZero k] (hk : 3 ≤ k) (F : Family k)
    (hnn : ∀ t : ZMod 3, IsNonneg (F t).edges)
    (hloop : ∀ (t : ZMod 3), ∀ e ∈ (F t).edges, e.1.1 ≠ e.1.2)
    (hsym : ∀ (t : ZMod 3) (x : Fin 3 → Fin k) (y : Fin k → Fin k),
      (F t).gval x y = (F t).gval (x ∘ Equiv.swap (1 : Fin 3) 2) y) :
    (0 < wbar F → ∀ δ : ℝ, 0 < δ →
      MaxKCutHard k ((∑ t : ZMod 3, Ct hk F t) / wbar F - δ) (maxS F / wbar F + δ)) ∧
    (0 < ∑ t : ZMod 3, Ct hk F t → ∀ δ : ℝ, 0 < δ →
      ∃ c s : ℝ, 0 < c ∧ s / c ≤ rho hk F + δ ∧ MaxKCutHard k c s) := by sorry

end Max3CutHard.Supplement
