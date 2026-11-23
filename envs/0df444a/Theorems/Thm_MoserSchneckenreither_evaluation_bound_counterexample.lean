-- Prove2me | Theorems.Thm_MoserSchneckenreither_evaluation_bound_counterexample
-- name    : MoserSchneckenreither.evaluation_bound_counterexample
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T08:58:07.878273+00:00
-- url     : https://prove2.me/theorems/d363cd4b-8cb9-4e58-b1fc-61c78b425743
-- title:
--   Corollary 6 — A numerical failure of the evaluation bound
-- statement:
--   There is a resource-bounded system and a typed initial term with a normalised substitution satisfying both closed-image consistency and the printed same-context condition. The instantiated term evaluates with one strict step to a normal form typable at the required annotation. One plus its whole-term potential exceeds the initial context potential plus the initial typing cost.
-- source:
--   Georg Moser and Manuel Schneckenreither, Automated amortised resource analysis for term rewrite systems, Science of Computer Programming 185 (2020), article 102306, https://doi.org/10.1016/j.scico.2019.102306. Counterexample to the numerical inequality of Corollary 6, p. 11, with Definition 3, p. 7.

import Definitions.Def_MoserSchneckenreither_Typing

namespace MoserSchneckenreither

theorem evaluation_bound_counterexample :
    ∃ (sig : Signature) (P : Problem sig) (F : AnnotatedSignature P) (Γ : Context)
      (σ : Substitution sig) (t v : Term sig) (q : Annotation) (k : ℚ≥0),
      ResourceBounded F ∧ σ.Normalised P ∧ Consistent F σ Γ ∧
      (∀ x ∈ σ.domain, ∀ p, (∃ j, Typing F .full Γ j (.var x) p) →
        ∃ j, Typing F .full Γ j (σ.apply x) p) ∧
      Typing F .full Γ k t q ∧ Derivation P (t.subst σ.apply) 1 v ∧ Normal P.rules v ∧
      (∃ j, Typing F .full [] j v q) ∧
      ¬ ((1 : ℚ≥0) + potential F v q ≤ contextPotential F σ Γ + k) := by sorry

end MoserSchneckenreither
