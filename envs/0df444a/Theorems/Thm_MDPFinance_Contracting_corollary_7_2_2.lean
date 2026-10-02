-- Prove2me | Theorems.Thm_MDPFinance_Contracting_corollary_7_2_2
-- name    : MDPFinance.Contracting.corollary_7_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:45:53.001334+00:00
-- url     : https://prove2.me/theorems/67804a6b-49a1-484d-b551-3aecae551fb7
-- title:
--   Corollary 7.2.2 — the discounted/negative-case specialization of Theorem 7.2.1
-- statement:
--   Theorem 7.2.1's two convergence hypotheses ($T_\circ^nb \to 0$, $\|\delta\|_b < \infty$) are
--   automatically satisfied whenever the upper bounding function is upper semicontinuous and
--   $\beta\alpha_b < 1$ — a purely algebraic condition on the model's own constants that covers, in
--   particular, the classical discounted case (bounded reward, $\beta < 1$) and the negative case
--   ($r \le 0$). This corollary is the version of Theorem 7.2.1 most directly applicable to a
--   concrete model, since $\beta\alpha_b < 1$ is usually the easiest of the hypotheses to check.
--
--   **Moderation note.** $E$ and $A$ are Borel spaces (Borel subsets of Polish spaces; the instance set of chunk `02b`), which the measurable selection in d) needs and which ties the topology to the $\sigma$-algebra; $\|\delta\|_b<\infty$ is stated as $\delta\le cb$ without demanding that $\delta$ be measurable (the book notes $J_n$, $J$, $J_\infty$ need not be in $\mathbb B$); conditions (ii) and (iii) are on $D$, where $Q$ and $r$ are defined.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 203, Corollary 7.2.2

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_MDPFinance_Contracting_LsSet

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.Contracting

/-- Corollary 7.2.2 (Bäuerle–Rieder, p. 203, PDF 214 (corrected from BRIEF.md's "p. 201")). Suppose the Markov Decision Model has an
usc upper bounding function `b` with `\beta\alpha_b < 1`. If conditions (i)-(iii) of Theorem
7.2.1 are satisfied, then all statements a)-d) of Theorem 7.2.1 are valid: `\beta\alpha_b < 1`
replaces Theorem 7.2.1's two convergence hypotheses (`T_\circ^nb \to 0`, `\|\delta\|_b < \infty`),
which it implies (p. 197's remark). Borel-space instances and conditions on `D` as in Theorem
7.2.1. -/
theorem corollary_7_2_2 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] [TopologicalSpace E]
    [BorelSpace E] [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [StandardBorelSpace E] [TopologicalSpace A] [BorelSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A] [StandardBorelSpace A]
    (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr αb) (hbusc : UpperSemicontinuous b)
    (hαb : M.β * αb < 1)
    (hDcompact : ∀ x, IsCompact (M.Dx x)) (hDusc : USCSetValued M.Dx)
    (hQusc : ∀ v ∈ IBbPlus b, UpperSemicontinuous v →
      UpperSemicontinuousOn (fun p : E × A => erealIntegral (M.Q p) v) M.D)
    (hrusc : UpperSemicontinuousOn M.r M.D) :
    (Jinf M ∈ IBbPlus b ∧ Jinf M = T M (Jinf M) ∧ Jinf M = Jlim M) ∧
      UpperSemicontinuous (Jinf M) ∧
      (∀ x, (LsSeq fun n => Dstar M (Jn M M.r n) x).Nonempty ∧
        LsSeq (fun n => Dstar M (Jn M M.r n) x) ⊆ Dstar M (Jinf M) x) ∧
      (∃ fstar : E → A, IsDecisionRuleOf M fstar ∧
        (∀ x, fstar x ∈ LsSeq fun n => Dstar M (Jn M M.r n) x) ∧
        ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) := by sorry

end MDPFinance.Contracting
