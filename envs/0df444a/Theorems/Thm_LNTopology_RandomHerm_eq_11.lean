-- Prove2me | Theorems.Thm_LNTopology_RandomHerm_eq_11
-- name    : LNTopology.RandomHerm.eq_11
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-14T10:15:26.75075+00:00
-- url     : https://prove2.me/theorems/d4e81000-8960-4e60-ab6f-b06bc0807b8c
-- title:
--   Proof of Theorem 3.9, (11) — P(g₊(d(i)) ≤ 2c(S(i))/c(s(i))) ≤ P((ε/2) g₊(d(i)) ≤ c(S(i)))
-- statement:
--   In the setting of Theorem 3.9 (a random Lightning Network $\Lambda(\omega)$ on a finite node set whose channels are exactly the edges of a simple graph $E$; $c$ a channel cost with (MO)–(SA), $g_+$ satisfying (SA+)), assume that for some $\varepsilon>0$ every channel satisfies
--   $$\mathbb P\big(c(\lambda_{i,j})>\varepsilon\big)=1\qquad(ij\in E).$$
--   Then for every node $i$ with $d(i)\ge 1$,
--   $$\mathbb P\Big(g_+(d(i))\le 2\,\frac{c(S(i))}{c(s(i))}\Big)\ \le\ \mathbb P\Big(\frac{\varepsilon}{2}\,g_+(d(i))\le c(S(i))\Big).$$
--
--   This is display (11): the uniform lower bound (ii) removes the random denominator $c(s(i))$ and reduces the failure probability of Lemma B.1's inequality at $i$ to a tail probability of the largest channel cost at $i$.
--
--   **Formalization Note** $d(i)$ is the degree of $i$ in $E$; $s(i)$ and $S(i)$ are the smallest and largest $|\lambda_{i,j}(\omega)|$ over the channels at $i$. The left event is the paper's $\{d(i)\le g_+^{-1}(2c(S(i))/c(s(i)))\}$ in $g_+$-form. Inequalities are between (outer) measures; no measurability is assumed. (SA) and (SA+) are in their corrected forms.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 13 (PDF 14), App. B.2, proof of Theorem 3.9, display (11)

import Mathlib
import Definitions.Def_LNTopology_Local_Model
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_RandomHerm_ChannelCost
import Definitions.Def_LNTopology_RandomHerm_Hermetization

open MeasureTheory

namespace LNTopology.RandomHerm

/-- Display (11) (proof of Theorem 3.9, p. 13): at a node `i` with `d(i) ≥ 1`, if every channel
satisfies `P(c(λ_{i,j}) > ε) = 1`, then
`P(g₊(d(i)) ≤ 2 c(S(i)) / c(s(i))) ≤ P((ε/2) g₊(d(i)) ≤ c(S(i)))`. -/
theorem eq_11 {V : Type} [Fintype V] [DecidableEq V] (E : SimpleGraph V) [DecidableRel E.Adj]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : Ω → V → V → ℝ) (c g : ℝ → ℝ) (hc : LNTopology.Local.IsChannelCost c) (hg : LNTopology.Hermetic.SAPlus c g)
    (hE : ∀ ω i j, Λ ω i j ≠ 0 ↔ E.Adj i j) (ε : ℝ) (hε : 0 < ε)
    (hii : ∀ i j, E.Adj i j → P {ω | ε < c (Λ ω i j)} = 1) (i : V) (hi : 0 < E.degree i) :
    P {ω | g (E.degree i) ≤
        2 * c (maxChanOn (Λ ω) Finset.univ i) / c (minChanOn (Λ ω) Finset.univ i)}
      ≤ P {ω | ε / 2 * g (E.degree i) ≤ c (maxChanOn (Λ ω) Finset.univ i)} := by sorry

end LNTopology.RandomHerm
