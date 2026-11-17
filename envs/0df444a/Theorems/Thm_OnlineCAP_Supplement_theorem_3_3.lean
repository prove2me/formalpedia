-- Prove2me | Theorems.Thm_OnlineCAP_Supplement_theorem_3_3
-- name    : OnlineCAP.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:22:29.677853+00:00
-- url     : https://prove2.me/theorems/3ea49f2c-a11e-48e4-865f-299f3ce689af
-- title:
--   Theorem 3.3 — Algorithm 1 is $O(\log n)$-competitive for OCycAP with cut arrivals
-- statement:
--   Let $A_L$ and $A_T$ be families of deterministic online algorithms for leftless and for topless rectangle hitting set with the two properties of Theorem 1.11 (no purchase on a satisfied rectangle and at most two otherwise; every point lies in $O(\log N)$ rectangles that are unsatisfied on arrival). Then there is a function $\alpha(n)=O(\log n)$ such that for every $n$ and every set $L$ of links (pairs of distinct vertices) on the cycle $v_0v_1\cdots v_{n-1}v_0$, each of cost $1$, **Algorithm 1** run with $A_L$ and $A_T$ buys only links of $L$, crosses every 2-cut requested so far, and on every valid sequence $C_1,\dots,C_t$ of 2-cuts buys
--
--   $$|F_t|\le\alpha(n)\cdot\mathrm{OPT}(C_1,\dots,C_t)$$
--
--   links.
--
--   With the algorithm of De, Singh and Tóth as subroutine, this is the cycle case of Theorem 1.4.
--
--   **Formalization Note** The ratio may depend on the subroutines (through the constants of their property 2) and on $n$ only.
--
--   Differences from the source:
--   - generalization: Algorithm 1 with the [DST25] algorithm, adapted by rotation, as subroutines → Algorithm 1 with any deterministic leftless and topless hitting families satisfying properties 1–2 of Theorem 1.11 (IsDSTHitter); reason: the paper specifies its subroutines only through these properties and the proof uses nothing else; by Theorem 1.11 the [DST25] subroutines satisfy them, so the statement specializes to the source
--   - reading: Algorithm 1 feeds R_L and R_T even when one of them contains no point of P → the subroutine properties are required on lists that may contain such rectangles (no hitting obligation, at most two purchases); reason: lines 10–11 of Algorithm 1 feed both rectangles; such a rectangle is never satisfied, so property 1 still applies, and it contains no point of P, so property 2 is unaffected
--   - encoding: a cycle G with |V| = n, k = 2, links L ⊆ (V choose 2), unit costs, ratio O(log n), C = [a, b] → the standard labelled cycle cycleEnds n with k = 2, L without diagonal pairs, c ≡ 1, ∃ α =O[atTop] Real.log, [a, b] computed by cutArc; reason: every cycle on the vertex set is a relabelling of the standard one; the published model of the mission
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 3.3, p.12 (PDF p.12); Algorithm 1, p.12; Theorem 1.11, p.11

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_RandOnlineAlg_IsDeterministic
import Definitions.Def_OnlineCAP_OnlineHSInstance
import Definitions.Def_OnlineCAP_OnlineHSInstance_OPT
import Definitions.Def_OnlineCAP_IsCompetitive
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_edgeCut
import Definitions.Def_OnlineCAP_IsKCut
import Definitions.Def_OnlineCAP_capInstance
import Definitions.Def_OnlineCAP_cycleEnds
import Definitions.Def_OnlineCAP_cycleInstance
import Definitions.Def_OnlineCAP_IsLeftless
import Definitions.Def_OnlineCAP_IsTopless
import Definitions.Def_OnlineCAP_RL
import Definitions.Def_OnlineCAP_RT
import Definitions.Def_OnlineCAP_linkPoint
import Definitions.Def_OnlineCAP_Supplement_IsDSTHitter
import Definitions.Def_OnlineCAP_Supplement_cutArc
import Definitions.Def_OnlineCAP_Supplement_algorithm1

open MeasureTheory Filter Asymptotics

namespace OnlineCAP.Supplement

/-- **Theorem 3.3 (Algorithm 1 is O(log n)-competitive for OCycAP with cut arrivals).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online
Connectivity Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…),
Theorem 3.3, p.12 (PDF p.12): "Algorithm 1 is an O(log n)-competitive algorithm for OCycAP with cut
arrivals."

Let `A_L` and `A_T` be families of deterministic online algorithms for leftless and for topless
rectangle hitting set with the two properties of Theorem 1.11 ([DST25], rotated). Then there is a
function `α(n) = O(log n)` such that for every `n` and every set `L` of links (pairs of distinct
vertices) on the cycle `v₀ v₁ ⋯ v_{n−1} v₀` with unit costs, Algorithm 1 run with `A_L`, `A_T`
buys only links of `L`, crosses every requested 2-cut, and buys at most `α(n) · OPT` links on
every valid sequence of 2-cuts.

**Formalization Note.** The paper specifies its subroutines (the [DST25] algorithm, adapted by
rotation) only through properties 1 and 2 of Theorem 1.11; they are the hypotheses
`IsDSTHitter IsLeftless A_L` and `IsDSTHitter IsTopless A_T`, with the `O(log N)` of property 2
an `IsBigO` bound uniform over point sets and fed lists. Theorem 1.11 itself is not assumed. The
ratio `α` may depend on the subroutines (through their constants) and on `n` only. The cycle is
the standard labelled cycle. -/
theorem theorem_3_3 (AL AT : ℕ → Finset (ℝ × ℝ) → RandOnlineAlg (ℝ × ℝ) (Set (ℝ × ℝ)))
    (hAL : IsDSTHitter IsLeftless AL) (hAT : IsDSTHitter IsTopless AT) :
    ∃ α : ℕ → ℝ, α =O[atTop] (fun n : ℕ => Real.log n) ∧
      ∀ (n : ℕ) (L : Finset (Sym2 (Fin n))), (∀ ℓ ∈ L, ¬ ℓ.IsDiag) →
        IsCompetitive (cycleInstance n L (fun _ => 1)) (algorithm1 AL AT n L) (α n) := by sorry

end OnlineCAP.Supplement
