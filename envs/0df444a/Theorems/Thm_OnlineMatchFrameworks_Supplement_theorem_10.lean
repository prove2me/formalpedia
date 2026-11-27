-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_Supplement_theorem_10
-- name    : OnlineMatchFrameworks.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:30:20.923804+00:00
-- url     : https://prove2.me/theorems/28ca1a4e-cf6f-43f5-9859-171035d67d20
-- title:
--   Theorem 10: against a clairvoyant who knows the patience the ratio is 0, also with infinite copies
-- statement:
--   A single customer has a random patience with known distribution. An online algorithm does not see the realization; a clairvoyant sees it in advance, but not the edge coins. For every $\varepsilon>0$:
--
--   1. there are a star with finitely many items and a patience distribution on the positive integers with
--
--   $$
--   0<\mathrm{CLAIR},\qquad \mathrm{OPT}_{\mathrm{online}}\le\varepsilon\,\mathrm{CLAIR};
--   $$
--
--   2. the same holds for some star in which every item has infinitely many copies.
--
--   Here $\mathrm{OPT}_{\mathrm{online}}$ is the supremum of the expected reward over all online algorithms and $\mathrm{CLAIR}$ is the expected reward of the best clairvoyant. So the competitive ratio against a clairvoyant is $0$, which is why Theorem 6 compares with a benchmark that does not know the patience.
--
--   Differences from the source:
--   - encoding: the optimal strategy of a single customer without knowledge of the patience → the published star optimum, the maximum over duplicate-free lists; reason: the only feedback while the customer is present is a failure, so lists are all the deterministic strategies (p.16)
--   - reading: the reward relative to a clairvoyant must be 0 → for every ε > 0 an instance with CLAIR > 0 and online optimum ≤ ε·CLAIR; reason: a competitive ratio is an infimum over instances, and the construction approaches 0 as k → ∞ (p.56)
--   - reading: even if there are infinite copies of every offline vertex → a second conjunct, in which lists may repeat items and both sides use such lists; reason: both settings are claimed (pp.32–33)
--   - encoding: θ drawn from an arbitrary distribution, with patience at least 1 (p.23, footnote 9) → the witnesses are laws of finite support on the positive integers; reason: the construction (8) has finite support; an existence claim with such a law is the source’s claim
--   - encoding: infinitely many copies, hence possibly unbounded offering sequences → a supremum over finite lists with repetition; reason: with bounded patience no longer list does better
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Theorem 10, p.32

import Definitions.Def_OnlineMatchFrameworks_Supplement_ClairvoyantStar
import Definitions.Def_OnlineMatchFrameworks_PatienceModels

namespace OnlineMatchFrameworks.Supplement

/-- **Theorem 10.** arXiv:1907.03963v6, Theorem 10, p.32: "For the star graph probing problem with
patience θ drawn from an arbitrary distribution, the reward of an online algorithm relative to a
clairvoyant who sees the realization of θ in advance must be 0, even if there are infinite copies of
every offline vertex."

**Formalization Note.** A ratio of `0` means: below every `ε > 0` on some instance. The first conjunct
is the star with finitely many items, the second the variant in which every item has infinitely many
copies. The online side is the optimum over all lists (lists are all the non-clairvoyant strategies
on a star, p.16), so it bounds every online algorithm. Both laws have finite support. -/
theorem theorem_10 :
    ∀ ε : ℝ, 0 < ε →
      (∃ (m : ℕ) (G : OnlineMatchFrameworks.Instance (Fin m) Unit) (μ : ℕ →₀ ℝ),
        IsPatienceLaw μ ∧
        (∀ l, G.surv () l = OnlineMatchFrameworks.tailSurvival (fun _ => lawTail μ) () l) ∧
        0 < clairvoyantStarValue G μ ∧
        G.starOpt Finset.univ () ≤ ε * clairvoyantStarValue G μ) ∧
      (∃ (m : ℕ) (G : OnlineMatchFrameworks.Instance (Fin m) Unit) (μ : ℕ →₀ ℝ),
        IsPatienceLaw μ ∧
        (∀ l, G.surv () l = OnlineMatchFrameworks.tailSurvival (fun _ => lawTail μ) () l) ∧
        0 < clairvoyantCopiesValue G μ ∧
        copiesOpt G ≤ ε * clairvoyantCopiesValue G μ) := by sorry

end OnlineMatchFrameworks.Supplement
