-- Prove2me | Theorems.Thm_LNTopology_RandomHerm_theorem_3_9
-- name    : LNTopology.RandomHerm.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:15:15.708215+00:00
-- url     : https://prove2.me/theorems/96d411c4-53df-4acf-80e9-738878379a19
-- title:
--   Theorem 3.9 — with power-law cost tails and a uniform cost floor, a random LN is hermetizable with probability ≥ 1 − k Σᵢ d(i) g₊(d(i))⁻ᵃ
-- statement:
--   Let $a>1$, $b>0$ and $\varepsilon>0$. There is a constant $k>0$, depending only on $a$, $b$ and $\varepsilon$, with the following property.
--
--   Let $V$ be a finite set of nodes and $E$ a simple graph on $V$ with at least one edge, the set of channels. Let $c$ be a channel cost with the properties (MO), (SY), (CI), (SA), and let $g_+$ satisfy (SA+) for $c$. Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $\Lambda(\omega)=(\lambda_{i,j}(\omega))$ a random Lightning Network: for every $\omega$ the matrix $\Lambda(\omega)$ is anti-symmetric, $\lambda_{i,j}(\omega)\neq 0$ exactly when $ij\in E$, and each $\lambda_{i,j}$ is a random variable. Assume that for all channels $ij\in E$
--   1. $\mathbb P\big(c(\lambda_{i,j})>x\big)<b\,x^{-a}$ for all $x>0$;
--   2. $\mathbb P\big(c(\lambda_{i,j})>\varepsilon\big)=1$.
--
--   Then the LN is hermetizable with probability at least
--   $$1-k\sum_{i\in V}d(i)\,\big(g_+(d(i))\big)^{-a},$$
--   where $d(i)$ is the degree of $i$ in $E$.
--
--   Since $g_+$ is increasing, the bound tends to $1$ when degrees are large relative to the tail exponent: under thin-tailed channel costs, cost reduction by a hub is the typical situation rather than the exception.
--
--   **Formalization Note** The constant $k$ is quantified after $a,b,\varepsilon$ and before the network, the law, $c$ and $g_+$; a $k$ allowed to depend on the network would make the statement trivial. The constants $a,b,\varepsilon$ are common to all channels. The paper's prose speaks of flows chosen independently with the same distribution, but the theorem's hypotheses are only (i) and (ii), and neither independence nor identical distribution is assumed. The channel set $E$ is fixed and deterministic, so $d(i)$ is deterministic. The hypothesis that $E$ has at least one channel is added: with no channel the printed bound equals $1$, yet the cost is $0$ and cannot be reduced. Isolated nodes contribute $0\cdot(\cdot)=0$ to the sum. The probability is `toReal` of a probability measure, evaluated on the event without assuming it measurable. (SA) and (SA+) are in their corrected forms: (SA) for all $x,y>0$; (SA+) for $k>1$, $x>0$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 8 (PDF 9), Theorem 3.9; proof on p. 13 (PDF 14), App. B.2

import Mathlib
import Definitions.Def_LNTopology_Local_Model
import Definitions.Def_LNTopology_Hermetic_Model
import Definitions.Def_LNTopology_RandomHerm_ChannelCost
import Definitions.Def_LNTopology_RandomHerm_Hermetization

open MeasureTheory

namespace LNTopology.RandomHerm

/-- Theorem 3.9 (p. 8). For tail parameters `a > 1`, `b > 0` and a floor `ε > 0` there is a
constant `k > 0`, depending only on `a, b, ε`, such that: for every finite channel graph `E`
with at least one channel, every cost `c` with (MO)–(SA+) for `g₊ = g`, and every random LN
`Λ` whose channels are exactly those of `E`, with
(i) `P(c(λ_{i,j}) > x) < b x^{-a}` for all `x > 0` and (ii) `P(c(λ_{i,j}) > ε) = 1` for every
channel `ij ∈ E`, the LN is hermetizable with probability at least
`1 − k Σ_i d(i) (g₊(d(i)))^{-a}`. -/
theorem theorem_3_9 :
    ∀ a b ε : ℝ, 1 < a → 0 < b → 0 < ε → ∃ k : ℝ, 0 < k ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (E : SimpleGraph V) [DecidableRel E.Adj]
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Λ : Ω → V → V → ℝ) (c g : ℝ → ℝ),
        LNTopology.Local.IsChannelCost c → LNTopology.Hermetic.SAPlus c g →
        (∀ ω, LNTopology.Local.IsLN (Λ ω)) →
        (∀ ω i j, Λ ω i j ≠ 0 ↔ E.Adj i j) →
        (∀ i j, Measurable fun ω => Λ ω i j) →
        (∀ i j, E.Adj i j → ∀ x : ℝ, 0 < x →
          P {ω | x < c (Λ ω i j)} < ENNReal.ofReal (b * x ^ (-a))) →
        (∀ i j, E.Adj i j → P {ω | ε < c (Λ ω i j)} = 1) →
        (∃ u v, E.Adj u v) →
        1 - k * ∑ i, (E.degree i : ℝ) * (g (E.degree i)) ^ (-a)
          ≤ (P {ω | IsHermetizableLN c (Λ ω)}).toReal := by sorry

end LNTopology.RandomHerm
