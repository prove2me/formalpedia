-- Prove2me | Theorems.Thm_LNTopology_RandomHerm_eq_12_13_max_tail
-- name    : LNTopology.RandomHerm.eq_12_13_max_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:15:01.825633+00:00
-- url     : https://prove2.me/theorems/aef48373-cf27-475d-972b-de642ed417e9
-- title:
--   Proof of Theorem 3.9, (12)–(13) — P(c(S(i)) ≥ x) ≤ d(i) b x⁻ᵃ
-- statement:
--   Let $\Lambda(\omega)$ be a random Lightning Network on a finite node set whose channels are exactly the edges of a simple graph $E$, and let $c$ be a channel cost with (MO)–(SA). Assume that for some $a>1$ and $b>0$ every channel satisfies the power-law tail bound
--   $$\mathbb P\big(c(\lambda_{i,j})>x\big)<b\,x^{-a}\qquad\text{for all }x>0\quad(ij\in E).$$
--   Then for every node $i$ and every $x>0$,
--   $$\mathbb P\big(c(S(i))\ge x\big)\ \le\ d(i)\,b\,x^{-a},$$
--   where $d(i)$ is the degree of $i$ and $S(i)$ the largest channel size at $i$.
--
--   This is displays (12)–(13): the largest channel cost at a node is a maximum over $d(i)$ channels, and a union bound transfers the per-channel tail to it.
--
--   **Formalization Note** The bound is stated in $[0,\infty]$ through `ENNReal.ofReal`. For an isolated node $S(i)$ takes the junk value $0$ and $c(0)=0<x$, so the event is empty and the bound holds trivially. The step from the strict tail $\mathbb P(c>x)$ in the hypothesis to the weak tail $\mathbb P(c\ge x)$ in the conclusion is the paper's; it is valid as stated. No measurability is assumed. (SA) is in its corrected form.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 13 (PDF 14), App. B.2, proof of Theorem 3.9, displays (12)–(13)

import Mathlib
import Definitions.Def_LNTopology_Local_Model
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_RandomHerm_ChannelCost
import Definitions.Def_LNTopology_RandomHerm_Hermetization

open MeasureTheory

namespace LNTopology.RandomHerm

/-- Displays (12)–(13) (proof of Theorem 3.9, p. 13): if every channel satisfies the tail bound
`P(c(λ_{i,j}) > x) < b x^{-a}` for all `x > 0`, then for every node `i` and every `x > 0`,
`P(c(S(i)) ≥ x) ≤ d(i) b x^{-a}`. -/
theorem eq_12_13_max_tail {V : Type} [Fintype V] [DecidableEq V] (E : SimpleGraph V)
    [DecidableRel E.Adj] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : Ω → V → V → ℝ) (c : ℝ → ℝ) (hc : LNTopology.Local.IsChannelCost c)
    (hE : ∀ ω i j, Λ ω i j ≠ 0 ↔ E.Adj i j) (a b : ℝ) (ha : 1 < a) (hb : 0 < b)
    (hi_tail : ∀ i j, E.Adj i j → ∀ x : ℝ, 0 < x →
      P {ω | x < c (Λ ω i j)} < ENNReal.ofReal (b * x ^ (-a)))
    (i : V) (x : ℝ) (hx : 0 < x) :
    P {ω | x ≤ c (maxChanOn (Λ ω) Finset.univ i)}
      ≤ ENNReal.ofReal ((E.degree i : ℝ) * b * x ^ (-a)) := by sorry

end LNTopology.RandomHerm
