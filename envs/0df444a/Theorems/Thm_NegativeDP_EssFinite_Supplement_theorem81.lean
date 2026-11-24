-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem81
-- name    : NegativeDP.EssFinite.Supplement.theorem81
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:01:45.678798+00:00
-- url     : https://prove2.me/theorems/cad2f525-bb89-4ad5-87bc-98202d593c4b
-- title:
--   Theorem 8.1 (D, P) — a (p, ε)-optimal stationary policy (D) and a (p, ε)-optimal semi-Markov policy (P)
-- statement:
--   For any probability $p$ on $S$ and any $\varepsilon>0$:
--
--   1. D. there is a $(p,\varepsilon)$-optimal stationary policy $f^{(\infty)}$;
--   2. P. there is a $(p,\varepsilon)$-optimal semi-Markov policy $\hat\pi$.
--
--   Here $\pi^*$ is $(p,\varepsilon)$-optimal if
--
--   $$
--   p\{I(\pi^*)\ge\sup_\pi I(\pi)-\varepsilon\}=1,
--   $$
--
--   the supremum over all policies; this is stronger than Blackwell's notion, which compares with each policy separately. The negative case of this theorem is the published item `NegativeDP.OptEq.theorem81`; together with this item it covers the whole source theorem.
--
--   **Formalization Note** `Disc.IsStrongPEOptimal` and `Pos.IsStrongPEOptimal` are the almost-everywhere comparison with `optReturn`, not Blackwell's `IsPOptimal`. The stationary policy is `(stationary f).toPlan`; `IsSemiMarkov` is the published non-random semi-Markov class.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, P, N → the cases not yet published (D and P); the negative case is the published NegativeDP.OptEq.theorem81; reason: the negative case is already published and immutable; the two items together state the whole theorem
--   - encoding: p{I(π*) ≥ v* − ε} = 1 in the completion of p → ∀ᵐ s ∂p, v* s − ε ≤ I π* s; reason: an a.e. statement is exactly a statement about the completion
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 884, Theorem 8.1

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_Stationary_Model
import Definitions.Def_NegativeDP_EssFinite_Supplement_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan Problem I T Ta U optReturn IsOptimal IsBM supNorm stationary IsGenerated IsGeneratedPlan)
open NegativeDP.Stationary (switchAt prefixPlan IsSemiMarkov IsMarkov IsRandomSemiMarkov IsRandomMarkov)

namespace NegativeDP.EssFinite.Supplement

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 8.1 (p. 884), discounted case (first conjunct: a `(p, ε)`-optimal stationary policy
`f^(∞)`) and positive bounded case (second conjunct: a `(p, ε)`-optimal semi-Markov policy),
for every `p ∈ P(S)` and `ε > 0`, with Strauch's `(p, ε)`-optimality
`p{I(π) ≥ v* − ε} = 1`. The negative case is the published `NegativeDP.OptEq.theorem81`. -/
theorem theorem81 :
    (∀ (P : Problem S A) (p : Measure S), IsProbabilityMeasure p → ∀ ε : ℝ, 0 < ε →
      ∃ f : {g : S → A // Measurable g}, Disc.IsStrongPEOptimal P p ε (stationary f).toPlan) ∧
    (∀ (P : Pos.Problem S A) (p : Measure S), IsProbabilityMeasure p → ∀ ε : ℝ, 0 < ε →
      ∃ πhat : Plan (S := S) (A := A), IsSemiMarkov πhat ∧ Pos.IsStrongPEOptimal P p ε πhat) := by sorry

end NegativeDP.EssFinite.Supplement
