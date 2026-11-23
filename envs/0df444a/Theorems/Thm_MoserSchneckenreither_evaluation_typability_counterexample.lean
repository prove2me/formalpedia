-- Prove2me | Theorems.Thm_MoserSchneckenreither_evaluation_typability_counterexample
-- name    : MoserSchneckenreither.evaluation_typability_counterexample
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T08:58:18.303745+00:00
-- url     : https://prove2.me/theorems/3b07d9be-6b09-4d36-9300-8b56f25efff7
-- title:
--   Corollary 6 — A normal form can lose its output annotation
-- statement:
--   There is a resource-bounded system and a typed initial term with a normalised substitution satisfying closed-image consistency and cost-preserving same-context consistency. The instantiated term evaluates with one strict step to a normal form. The whole-term resource inequality holds with equality, but the normal form has no closed typing at the original output annotation at any cost.
-- source:
--   Georg Moser and Manuel Schneckenreither, Automated amortised resource analysis for term rewrite systems, Science of Computer Programming 185 (2020), article 102306, https://doi.org/10.1016/j.scico.2019.102306. Counterexample to the typability conclusion of Corollary 6, p. 11, with nonlinear rules.

import Definitions.Def_MoserSchneckenreither_Typing

namespace MoserSchneckenreither

theorem evaluation_typability_counterexample :
    ∃ (sig : Signature) (P : Problem sig) (F : AnnotatedSignature P) (Γ : Context)
      (σ : Substitution sig) (t v : Term sig) (q : Annotation) (k : ℚ≥0),
      ResourceBounded F ∧ σ.Normalised P ∧ Consistent F σ Γ ∧
      (∀ x ∈ σ.domain, ∀ p j, Typing F .full Γ j (.var x) p →
        Typing F .full Γ j (σ.apply x) p) ∧
      Typing F .full Γ k t q ∧ Derivation P (t.subst σ.apply) 1 v ∧ Normal P.rules v ∧
      ((1 : ℚ≥0) + potential F v q = contextPotential F σ Γ + k) ∧
      ¬ ∃ j, Typing F .full [] j v q := by sorry

end MoserSchneckenreither
