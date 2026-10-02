-- Prove2me | Theorems.Thm_MDPFinance_Contracting_theorem_7_2_1
-- name    : MDPFinance.Contracting.theorem_7_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:46:10.25299+00:00
-- url     : https://prove2.me/theorems/147e22d5-a5b8-4fb3-a226-f1eb5fe9d277
-- title:
--   Theorem 7.2.1 — semicontinuous existence, value iteration, and policy iteration
-- statement:
--   This theorem gives verifiable, primitive conditions on the model's own data — compactness and
--   upper semicontinuity of the feasible correspondence $D(\cdot)$, of the one-step transition
--   integral, and of the reward — under which the abstract Structure Assumption (SA) of Theorem
--   7.1.8 automatically holds for $IM := IB_b^+$, so value iteration converges to the true value
--   $J_\infty$. It additionally identifies which actions the finite-horizon optimal policies converge
--   to: the upper limit $\mathrm{Ls}\,D_n^*(x)$ of the finite-stage optimal-action sets is always
--   non-empty and contained in the infinite-horizon optimal-action set $D_\infty^*(x)$ — this is
--   **policy iteration**, the practical payoff of the whole existence theory: an optimal
--   infinite-horizon policy can be approximated by solving longer and longer finite-horizon problems.
--
--   **Moderation note.** $E$ and $A$ are Borel spaces (Borel subsets of Polish spaces; the instance set of chunk `02b`), which the measurable selection in d) needs and which ties the topology to the $\sigma$-algebra; $\|\delta\|_b<\infty$ is stated as $\delta\le cb$ without demanding that $\delta$ be measurable (the book notes $J_n$, $J$, $J_\infty$ need not be in $\mathbb B$); conditions (ii) and (iii) are on $D$, where $Q$ and $r$ are defined.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 201, Theorem 7.2.1

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_MDPFinance_Contracting_LsSet

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.Contracting

/-- Theorem 7.2.1 (Bäuerle–Rieder, p. 201, PDF 212 (corrected from BRIEF.md's "p. 199")). Let `E`, `A` be Borel (here: topological)
spaces, `D` a Borel subset of `E \times A`. Suppose there exists an upper bounding function `b`
with `T_\circ^nb \to 0`, `\|\delta\|_b < \infty` (i.e. `δ ≤ c b` for some `c`; `δ` need not be
known measurable) and (i) `D(x)`
compact, `x \mapsto D(x)` usc, (ii) `(x,a) \mapsto \int v(x')Q(dx'|x,a)` usc for all usc `v \in
IB_b^+`, (iii) `(x,a) \mapsto r(x,a)` usc. Then it holds: a) `J_\infty \in IB_b^+`, `J_\infty =
TJ_\infty` and `J_\infty = J` (Value Iteration). b) If `b` is usc then `J_\infty` is usc. c)
`\emptyset \ne \mathrm{Ls}\,D_n^*(x) \subset D_\infty^*(x)` for all `x \in E` (Policy Iteration).
d) There exists `f^* \in F` with `f^*(x) \in \mathrm{Ls}\,D_n^*(x)` for all `x \in E`, and the
stationary policy `(f^*,f^*,\dots)` is optimal. `D_n^*(x)`/`D_\infty^*(x)` render `Dstar M
(Jn M M.r n) x`/`Dstar M (Jinf M) x`, the sequence reindexed by `n` directly (rather than
`n-1`) — a shift-invariant relabeling, see `MODERATION_NOTES.md`. `E`, `A` are Borel spaces (Borel
subsets of Polish spaces, the instances of chunk `02b`); (ii), (iii) are conditions on `D`. -/
theorem theorem_7_2_1 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] [TopologicalSpace E]
    [BorelSpace E] [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [StandardBorelSpace E] [TopologicalSpace A] [BorelSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A] [StandardBorelSpace A]
    (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr αb)
    (hTcirc : ∀ x, Tendsto (fun n => (Tcirc M)^[n] (fun y => (b y : EReal)) x) atTop (𝓝 (0 : EReal)))
    (hδb : ∃ c : ℝ, 0 ≤ c ∧ ∀ x, delta M x ≤ ((c * b x : ℝ) : EReal))
    (hDcompact : ∀ x, IsCompact (M.Dx x)) (hDusc : USCSetValued M.Dx)
    (hQusc : ∀ v ∈ IBbPlus b, UpperSemicontinuous v →
      UpperSemicontinuousOn (fun p : E × A => erealIntegral (M.Q p) v) M.D)
    (hrusc : UpperSemicontinuousOn M.r M.D) :
    (Jinf M ∈ IBbPlus b ∧ Jinf M = T M (Jinf M) ∧ Jinf M = Jlim M) ∧
      (UpperSemicontinuous b → UpperSemicontinuous (Jinf M)) ∧
      (∀ x, (LsSeq fun n => Dstar M (Jn M M.r n) x).Nonempty ∧
        LsSeq (fun n => Dstar M (Jn M M.r n) x) ⊆ Dstar M (Jinf M) x) ∧
      (∃ fstar : E → A, IsDecisionRuleOf M fstar ∧
        (∀ x, fstar x ∈ LsSeq fun n => Dstar M (Jn M M.r n) x) ∧
        ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) := by sorry

end MDPFinance.Contracting
