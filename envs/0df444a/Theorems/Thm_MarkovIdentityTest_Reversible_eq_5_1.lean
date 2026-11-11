-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_eq_5_1
-- name    : MarkovIdentityTest.Reversible.eq_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:39:30.206434+00:00
-- url     : https://prove2.me/theorems/506b10c4-569c-4fac-9a07-81c8ef29d400
-- title:
--   §5.1 Eq. (5.1) — the stopped-row law: geometric retained length, i.i.d. returning destinations, final destination from $e$
-- statement:
--   Let $Q$ be stochastic, $x$ an initial state, $i$ a source state, and $T$ an independent positive geometric time of mean $M\ge1$. Let $N$ be the number of departures from $i$ before $T$ and $Y_1,\dots,Y_N$ their destinations. For a destination $y$ let $h_y$ be the probability that, after the transition $i\to y$, the trajectory returns to $i$ and departs from $i$ again before $T$; put $s=\sum_yQ_{iy}h_y$, $r_y=Q_{iy}h_y/s$ and $e_y=Q_{iy}(1-h_y)/(1-s)$. Then for every $k\ge1$ and $y_1,\dots,y_k$
--   $$\Pr(N=k,Y_1=y_1,\dots,Y_k=y_k\mid N\ge1)=(1-s)s^{k-1}\prod_{a=1}^{k-1}r_{y_a}\,e_{y_k},$$
--   and with $L=(N-1)_+$: $\Pr(L=l\mid N\ge1)=(1-s)s^l$, and conditionally on $L=l$ the retained destinations $Y_1,\dots,Y_l$ are i.i.d. with law $r$ while the deleted one has law $e$:
--   $$\Pr(N=l+1,Y=y)=\Pr(N=l+1)\prod_{a\le l}r_{y_a}\,e_{y_{l+1}}.$$
--   This regeneration fact makes each retained row analyzable.
--
--   Differences from the source:
--
--   - encoding: Pr(· | N ≥ 1) → Pr(· and N ≥ 1) = Pr(N ≥ 1) × right side; reason: equivalent whenever Pr(N ≥ 1) > 0, which conditioning presupposes; at Pr(N ≥ 1) = 0 both sides are 0
--   - reading: h_y: after i → y, the probability of returning to i and departing again before T → the chain from y is at i at some time u < T' − 1, with T' a fresh positive geometric time of mean M; reason: memorylessness of T: after an observed transition the number of transitions still observed is T' − 1
--   - encoding: k ≥ 1 destinations y_1, …, y_k → l + 1 destinations y : Fin (l + 1) → Fin n, k = l + 1; reason: 0-based indexing
--   - encoding: positive geometric T of mean M → M ∈ ℝ, M ≥ 1, Pr(T = t) = M⁻¹(1 − M⁻¹)^{t−1}; reason: M ≥ 1 is exactly the range where this is a probability law
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 24, §5.1, Eq. (5.1) and the paragraph after it

import Mathlib
import Definitions.Def_CEPolytopeHard_IsStochastic
import Definitions.Def_MarkovIdentityTest_Reversible_Trajectory
import Definitions.Def_MarkovIdentityTest_Reversible_StoppedRow

set_option autoImplicit false

open CEPolytopeHard

namespace MarkovIdentityTest.Reversible

/-- §5.1, Eq. (5.1) and the two sentences after it (Jia, p. 24 / PDF 26): the law of the
departures from a source state `i` up to an independent positive geometric time of mean `M`.
Conditional probabilities given `N ≥ 1` are written multiplied out. -/
theorem eq_5_1 {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsStochastic Q) (M : ℝ) (hM : 1 ≤ M)
    (x i : Fin n) :
    (∀ (l : ℕ) (y : Fin (l + 1) → Fin n),
      geomProb M Q x (fun _ ω => departureDests ω i = List.ofFn y) =
        geomProb M Q x (fun _ ω => 1 ≤ departures ω i) *
          ((1 - returnMass M Q i) * returnMass M Q i ^ l *
            (∏ a : Fin l, returnLaw M Q i (y a.castSucc)) * finalLaw M Q i (y (Fin.last l)))) ∧
    (∀ l : ℕ,
      geomProb M Q x (fun _ ω => departures ω i = l + 1) =
        geomProb M Q x (fun _ ω => 1 ≤ departures ω i) *
          ((1 - returnMass M Q i) * returnMass M Q i ^ l)) ∧
    (∀ (l : ℕ) (y : Fin (l + 1) → Fin n),
      geomProb M Q x (fun _ ω => departureDests ω i = List.ofFn y) =
        geomProb M Q x (fun _ ω => departures ω i = l + 1) *
          ((∏ a : Fin l, returnLaw M Q i (y a.castSucc)) * finalLaw M Q i (y (Fin.last l)))) := by sorry

end MarkovIdentityTest.Reversible
