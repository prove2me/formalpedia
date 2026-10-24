-- Prove2me | Theorems.Thm_LNTopology_RandomHerm_eq_8_10_union_bound
-- name    : LNTopology.RandomHerm.eq_8_10_union_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:15:13.999671+00:00
-- url     : https://prove2.me/theorems/4863b2ca-4746-4202-a361-7edd89ed7cb9
-- title:
--   Proof of Theorem 3.9, (8)–(10) — P(hermetizable) ≥ 1 − Σᵢ P(g₊(d(i)) ≤ 2c(S(i))/c(s(i)))
-- statement:
--   Let $E$ be a simple graph on the finite node set $V$ with at least one edge, the set of channels. Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $\Lambda(\omega)=(\lambda_{i,j}(\omega))$ a random Lightning Network whose channels are exactly the edges of $E$: for every $\omega$, $\Lambda(\omega)$ is anti-symmetric and $\lambda_{i,j}(\omega)\neq 0$ if and only if $ij\in E$. Let $c$ be a channel cost with (MO)–(SA) and $g_+$ satisfy (SA+). Write $d(i)$ for the degree of $i$ in $E$ and $s(i)$, $S(i)$ for the smallest and largest channel sizes at $i$ in $\Lambda(\omega)$. Then
--   $$\mathbb P\big(\Lambda\ \text{is hermetizable}\big)\ \ge\ 1-\sum_{i:\,d(i)\ge 1}\mathbb P\Big(g_+(d(i))\le 2\,\frac{c(S(i))}{c(s(i))}\Big).$$
--
--   This is the union-bound step (8)–(10) of the proof of Theorem 3.9, combined with Lemma B.1: on the event that every node with a channel satisfies Lemma B.1's inequality, the set of such nodes is hermetizable.
--
--   **Formalization Note** The sum runs over nodes with at least one channel: for an isolated node $s(i)$ is undefined, and isolated nodes play no role in the hermetized set. The event $d(i)\le g_+^{-1}(\cdot)$ is written $g_+(d(i))\le\cdot$ (see Lemma B.1). Probabilities are real numbers via `toReal` of a probability measure; no measurability of the event is assumed (a lower bound on the outer measure). The hypotheses (i), (ii) of Theorem 3.9 are not needed for this step and are omitted. The paper writes $C(S(i))$ for $c(S(i))$ in (8)–(10). (SA) and (SA+) are in their corrected forms.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 13 (PDF 14), App. B.2, proof of Theorem 3.9, displays (8)–(10)

import Mathlib
import Definitions.Def_LNTopology_Local_Model
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_RandomHerm_ChannelCost
import Definitions.Def_LNTopology_RandomHerm_Hermetization

open MeasureTheory

namespace LNTopology.RandomHerm

/-- Displays (8)–(10) (proof of Theorem 3.9, p. 13): by Lemma B.1 applied to the set of nodes
that have a channel, the random LN is hermetizable with probability at least
`1 − Σ_{i : d(i) ≥ 1} P(g₊(d(i)) ≤ 2 c(S(i)) / c(s(i)))`. -/
theorem eq_8_10_union_bound {V : Type} [Fintype V] [DecidableEq V] (E : SimpleGraph V)
    [DecidableRel E.Adj] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : Ω → V → V → ℝ) (c g : ℝ → ℝ) (hc : LNTopology.Local.IsChannelCost c) (hg : LNTopology.Hermetic.SAPlus c g)
    (hLN : ∀ ω, LNTopology.Local.IsLN (Λ ω)) (hE : ∀ ω i j, Λ ω i j ≠ 0 ↔ E.Adj i j)
    (hchan : ∃ u v, E.Adj u v) :
    1 - ∑ i ∈ Finset.univ.filter (fun i => 0 < E.degree i),
        (P {ω | g (E.degree i) ≤
          2 * c (maxChanOn (Λ ω) Finset.univ i) / c (minChanOn (Λ ω) Finset.univ i)}).toReal
      ≤ (P {ω | IsHermetizableLN c (Λ ω)}).toReal := by sorry

end LNTopology.RandomHerm
