-- Prove2me | Theorems.Thm_MDPFinance_Contracting_theorem_7_2_3
-- name    : MDPFinance.Contracting.theorem_7_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:45:59.847771+00:00
-- url     : https://prove2.me/theorems/747a39e3-2713-4c9c-a4f5-d4a5a8050ba9
-- title:
--   Theorem 7.2.3 — the purely-measurable analogue of Theorem 7.2.1
-- statement:
--   This variant of Theorem 7.2.1 drops the topological hypotheses on the correspondence $x \mapsto
--   D(x)$ itself (upper semicontinuity of the feasible set as $x$ varies), keeping only compactness
--   of each $D(x)$ and semicontinuity of the transition integral and reward *in the action alone*,
--   for each fixed state. The price is a slightly weaker conclusion: the theorem no longer asserts
--   $J_\infty$ is upper semicontinuous even when $b$ is, since that part of Theorem 7.2.1's proof
--   genuinely used joint semicontinuity in $(x,a)$. Value iteration and policy iteration still hold.
--
--   **Moderation note.** $E$ standard Borel and $A$ a Borel space (needed for the measurable selection in c)); $\|\delta\|_b<\infty$ stated as $\delta\le cb$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 203, Theorem 7.2.3

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_MDPFinance_Contracting_LsSet

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.Contracting

/-- Theorem 7.2.3 (Bäuerle–Rieder, p. 203, PDF 214 (corrected from BRIEF.md's "p. 201")), the purely-measurable analogue of Theorem
7.2.1 (no topology on `D(\cdot)` itself, only on `a \mapsto \dots` for fixed `x`). Suppose there
exists an upper bounding function `b` with `T_\circ^nb \to 0`, `\|\delta\|_b < \infty` and (i)
`D(x)` compact, (ii) `a \mapsto \int v(x')Q(dx'|x,a)` usc for all `v \in IB_b^+` and every `x`,
(iii) `a \mapsto r(x,a)` usc for every `x`. Then it holds: a) `J_\infty \in IB_b^+`, `J_\infty =
TJ_\infty` and `J = J_\infty` (Value Iteration). b) `\emptyset \ne \mathrm{Ls}\,D_n^*(x) \subset
D_\infty^*(x)` (Policy Iteration). c) There exists `f^* \in F` with `f^*(x) \in \mathrm{Ls}\,
D_n^*(x)`, and `(f^*,f^*,\dots)` is optimal. `E`, `A` Borel spaces; `\|\delta\|_b < \infty` as
`δ ≤ c b`. -/
theorem theorem_7_2_3 {E A : Type*} [MeasurableSpace E] [StandardBorelSpace E] [MeasurableSpace A]
    [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A]
    (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ) (hb : IsUpperBoundingFunction M b cr αb)
    (hTcirc : ∀ x, Tendsto (fun n => (Tcirc M)^[n] (fun y => (b y : EReal)) x) atTop (𝓝 (0 : EReal)))
    (hδb : ∃ c : ℝ, 0 ≤ c ∧ ∀ x, delta M x ≤ ((c * b x : ℝ) : EReal))
    (hDcompact : ∀ x, IsCompact (M.Dx x))
    (hQusc : ∀ v ∈ IBbPlus b, ∀ x, UpperSemicontinuousOn (fun a => erealIntegral (M.Q (x, a)) v)
      (M.Dx x))
    (hrusc : ∀ x, UpperSemicontinuousOn (fun a => M.r (x, a)) (M.Dx x)) :
    (Jinf M ∈ IBbPlus b ∧ Jinf M = T M (Jinf M) ∧ Jlim M = Jinf M) ∧
      (∀ x, (LsSeq fun n => Dstar M (Jn M M.r n) x).Nonempty ∧
        LsSeq (fun n => Dstar M (Jn M M.r n) x) ⊆ Dstar M (Jinf M) x) ∧
      (∃ fstar : E → A, IsDecisionRuleOf M fstar ∧
        (∀ x, fstar x ∈ LsSeq fun n => Dstar M (Jn M M.r n) x) ∧
        ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) := by sorry

end MDPFinance.Contracting
