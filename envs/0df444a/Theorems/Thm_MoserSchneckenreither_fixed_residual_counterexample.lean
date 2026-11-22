-- Prove2me | Theorems.Thm_MoserSchneckenreither_fixed_residual_counterexample
-- name    : MoserSchneckenreither.fixed_residual_counterexample
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T08:57:51.962266+00:00
-- url     : https://prove2.me/theorems/9a328890-7349-4524-9973-2d7911be1537
-- title:
--   Theorem 5 — Fixed residual typing can exceed the budget
-- statement:
--   With rootwise potential, a resource-bounded relative system admits a one-step instance between a typed source and a fixed residual term with normalised substitutions at both ends. The initial substitution satisfies closed-image and printed same-context consistency. For the fixed residual term and substitution there is no residual context, cost, or output annotation that satisfies both full typing and the rootwise resource inequality with charge one.
-- source:
--   Georg Moser and Manuel Schneckenreither, Automated amortised resource analysis for term rewrite systems, Science of Computer Programming 185 (2020), article 102306, https://doi.org/10.1016/j.scico.2019.102306. Counterexample to the fixed-residual reading of Theorem 5, pp. 10–11, after replacing the potential of Definition 3 by its rootwise variant.

import Definitions.Def_MoserSchneckenreither_Typing
import Definitions.Def_MoserSchneckenreither_RootPotential

namespace MoserSchneckenreither

theorem fixed_residual_counterexample :
    ∃ (sig : Signature) (P : Problem sig) (F : AnnotatedSignature P) (Γ : Context)
      (σ τ : Substitution sig) (t u : Term sig) (p : Annotation) (k : ℚ≥0),
      ResourceBounded F ∧ σ.Normalised P ∧ τ.Normalised P ∧ Consistent F σ Γ ∧
      (∀ x ∈ σ.domain, ∀ q, (∃ j, Typing F .full Γ j (.var x) q) →
        ∃ j, Typing F .full Γ j (σ.apply x) q) ∧
      Typing F .full Γ k t p ∧ RelativeStep P (t.subst σ.apply) (u.subst τ.apply) ∧
      ¬ ∃ (Δ : Context) (ℓ : ℚ≥0) (q : Annotation), Typing F .full Δ ℓ u q ∧
        rootContextPotential F τ.apply Δ + ℓ + 1 ≤ rootContextPotential F σ.apply Γ + k := by sorry

end MoserSchneckenreither
