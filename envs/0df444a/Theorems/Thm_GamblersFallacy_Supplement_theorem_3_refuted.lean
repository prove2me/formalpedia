-- Prove2me | Theorems.Thm_GamblersFallacy_Supplement_theorem_3_refuted
-- name    : GamblersFallacy.Supplement.theorem_3_refuted
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:14:09.717673+00:00
-- url     : https://prove2.me/theorems/1c86d6b0-819b-47c2-b214-639ff4d9721e
-- title:
--   Theorem 3 (corrected: refuted, $W^*(2)=1<W^*=3$) — the finite-horizon optimal delay $W^*(n)$ can be shorter than the long-run optimal delay $W^*$
-- statement:
--   Theorem 3 of the paper asserts that $W^*(n)\ge W^*$ for all $n$. Here $W^*(n)$ is the optimal delay of the delay ordering policy for the $n$-period cost per cycle $F_n(W)$, and $W^*$ is the optimal delay for the long-run cost per cycle $L(W)$. The assertion is false:
--
--   1. There are an inter-arrival law with $p_j>0$ for all $j\in\{1,\dots,J\}$, costs $b,h>0$, a horizon $n\ge1$, a minimizer $W_n$ of $F_n$ over $W\in\mathbb N$ and a minimizer $W$ of $L$ over $W\in\mathbb N$ with $W>W_n$.
--   2. An instance is $J=4$, $(p_1,p_2,p_3,p_4)=(3/11,\,4/11,\,1/22,\,7/22)$, $b=8$, $h=7$, $n=2$. Then $F_2(0)=1008/121$, $F_2(1)=476/121$ and $F_2(W)=520/121$ for every $W\ge2$, so $W^*(2)=1$ is the unique minimizer:
--   $$
--   F_2(1)<F_2(W)\quad (W\ne1).
--   $$
--   Also $L(0),\dots,L(3)=217/22,\,153/22,\,161/22,\,60/11$ and $L(W)=8$ for every $W\ge4$, so $W^*=3$ is the unique minimizer:
--   $$
--   L(3)<L(W)\quad(W\ne3).
--   $$
--
--   The same instance also refutes the claim under the other reading of $C_{\mathrm{tail}}$, the one in the proof of Proposition 3, where a truncated last cycle costs nothing. That finite-horizon cost is Proposition 3's formula $b\sum_{j\le W}p_j(n)+h\sum_{j=W+2}^n(j-W-1)p_j(n)$. Its values at $n=2$ are $28/11$, $168/121$, and then $520/121$ for $W\ge2$, so its unique minimizer is again $1$.
--
--   Since both minimizers are unique, the refutation holds for every tie-breaking rule. The paper's argument (EC.2.3) compares the backorder and holding cost components at a fixed $W$ and does not compare minimizers.
--
--   **Formalization Note** Delays range over $W\in\mathbb N$, where $W=0$ is immediate replenishment. $F_n$ is `finiteHorizonCost` (the definition on p.15), its closed-cycle variant is `finiteHorizonCostClosed`, and $L$ is `longRunCost`.
--
--   Differences from the source:
--   - correction: $W^*(n)\ge W^*$ for all $n$ → its negation, with the instance $n=2$, $p=(3/11,4/11,1/22,7/22)$, $b=8$, $h=7$, where the minimizers are unique: $W^*(2)=1<W^*=3$; reason: the printed statement is false. The values are $F_2=1008/121,\,476/121$ and then $520/121$ for $W\ge2$, and $L=217/22,\,153/22,\,161/22,\,60/11$ and then $8$ for $W\ge4$, computed in exact arithmetic and checked in Lean at $W=1,3$
--   - reading: "the optimal delay" $W^*(n)$, $W^*$ → any minimizer over $W\in\mathbb N$; reason: the paper fixes no tie rule; the negation quantifies over all minimizers, and in the instance both are unique
--   - reading: $C_{\mathrm{tail}}$ = "the cost from the last arrival period $\sum_{t\le\tau}Z_t+1$ to the end of horizon period $n$" → the full cycle cost if the next demand falls at $n$, else the holding cost $h\max\{0,n-\sum_{t\le\tau}Z_t-W\}$ (`finiteHorizonCost`), and in part 2 also the reading of the proof of Proposition 3, where a truncated last cycle costs $0$ (`finiteHorizonCostClosed`, equal to Proposition 3's formula); reason: under $\pi_{adp}$ the first is the inventory cost of those periods, and the proof of Proposition 3 uses the second. In the instance both have the unique minimizer $1$ ($28/11$, $168/121$, then $520/121$ for the second), so the refutation holds under either reading
--   - encoding: "for all $n$" → horizons $n\ge1$ in the negated claim; reason: an $n$-period problem has at least one period, and restricting the claim only strengthens its negation
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, Theorem 3, p.16 (proof EC.2.3, p.ec5); W*(n), W*, p.16; π_adp and its costs, p.15

import Mathlib
import Definitions.Def_GamblersFallacy_Supplement_RenewalLaw
import Definitions.Def_GamblersFallacy_Supplement_DelayPolicy

namespace GamblersFallacy.Supplement

/-- **Theorem 3 (corrected: refuted, `W*(2) = 1 < W* = 3`) — the finite-horizon optimal delay can be shorter than the long-run
one.**
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, Theorem 3, p.16: "W*(n) ≥ W* for all n",
where (p.16) "W*(n) denote[s] the optimal delay for an n-period problem, and W* the optimal delay
policy for a long run average cycle cost model".

The statement is false. Part 1 is its negation for every choice of minimizers: there are an
inter-arrival law with every `p_j > 0`, costs `b, h > 0`, a horizon `n ≥ 1`, a minimizer `W_n` of
the finite-horizon cost per cycle and a minimizer `W` of the long-run cost per cycle with
`W > W_n`. Part 2 gives the instance: `J = 4`, `p = (3/11, 4/11, 1/22, 7/22)`, `b = 8`, `h = 7`,
`n = 2`. There the finite-horizon cost has the unique minimizer `W*(2) = 1` and the long-run
cost the unique minimizer `W* = 3`. Part 2 also shows that the refutation does not depend on how
`C_tail` is read: with `C_tail` charged only on a closed last cycle (the reading in the proof of
Proposition 3, `finiteHorizonCostClosed`, values `28/11, 168/121` and `520/121` for `W ≥ 2`), the
unique finite-horizon minimizer is again `1`.

**Formalization Note.** Delays range over `W ∈ ℕ` (`W = 0` is immediate replenishment). The
finite-horizon cost is the paper's definition on p.15 (`finiteHorizonCost`), the long-run cost is
`b Σ_{j≤W} p_j + h p_{W+2} + 2h p_{W+3} + ⋯` (`longRunCost`). -/
theorem theorem_3_refuted :
    (¬ ∀ L : InterArrivalLaw, (∀ j ∈ Finset.Icc 1 L.J, 0 < L.p j) →
        ∀ b h : ℝ, 0 < b → 0 < h → ∀ n : ℕ, 1 ≤ n → ∀ Wn W : ℕ,
          (∀ V : ℕ, finiteHorizonCost L b h n Wn ≤ finiteHorizonCost L b h n V) →
          (∀ V : ℕ, longRunCost L b h W ≤ longRunCost L b h V) → W ≤ Wn) ∧
    (∃ L : InterArrivalLaw, L.J = 4 ∧ L.p 1 = 3 / 11 ∧ L.p 2 = 4 / 11 ∧ L.p 3 = 1 / 22 ∧
      L.p 4 = 7 / 22 ∧
      (∀ V : ℕ, V ≠ 1 → finiteHorizonCost L 8 7 2 1 < finiteHorizonCost L 8 7 2 V) ∧
      (∀ V : ℕ, V ≠ 3 → longRunCost L 8 7 3 < longRunCost L 8 7 V) ∧
      (∀ V : ℕ, V ≠ 1 →
        finiteHorizonCostClosed L 8 7 2 1 < finiteHorizonCostClosed L 8 7 2 V)) := by sorry

end GamblersFallacy.Supplement
