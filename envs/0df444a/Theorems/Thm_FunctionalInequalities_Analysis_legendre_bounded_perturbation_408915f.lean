-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_bounded_perturbation_408915f
-- name    : FunctionalInequalities.Analysis.legendre_bounded_perturbation_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:25.129889+00:00
-- url     : https://prove2.me/theorems/0f2df289-7a5e-45b9-9b89-7b9c83c87761
-- title:
--   Bounded Perturbation of the Extended-Real Legendre Transform
-- statement:
--   This states the uniform perturbation bound for the actual extended-real Legendre transform.
--
--   Let $E$ be a real inner-product space, let $\phi:E\to\overline{\mathbb R}$ be a proper potential, and let $b:E\to\mathbb R$. If $M\geq0$ and $|b(z)|\leq M$ for every $z$, then for every $t\in\mathbb R$ and $q\in E$,
--
--   $$
--   \operatorname{Leg}(\phi)(q)-|t|M
--   \leq
--   \operatorname{Leg}(z\mapsto\phi(z)+t b(z))(q)
--   \leq
--   \operatorname{Leg}(\phi)(q)+|t|M.
--   $$
--
--   The inequalities hold in `EReal`, including infinite values; no convexity or global finiteness of $\phi$ is assumed. This gives a direct stability estimate for bounded perturbations of the conjugate.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Perturbation.lean#L62-L113 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Perturbation`, declaration `FunctionalInequalities.Analysis.legendre_bounded_perturbation`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section BoundedPerturbation
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.legendre_bounded_perturbation_408915f
    (φ : E → EReal) (hφ : ProperPotential φ)
    (b : E → ℝ) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ z : E, |b z| ≤ M) :
    ∀ (t : ℝ) (q : E),
      legendre φ q - ((|t| * M : ℝ) : EReal) ≤
          legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q ∧
        legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q ≤
          legendre φ q + ((|t| * M : ℝ) : EReal) := by sorry
