-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_bounded_perturbation_readable
-- name    : FunctionalInequalities.Analysis.legendre_bounded_perturbation_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:32.138414+00:00
-- url     : https://prove2.me/theorems/e3dacbfa-f2d9-4678-b1ae-2ca5c68e3e32
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem legendre_bounded_perturbation
--       (φ : E → EReal) (hφ : ProperPotential φ)
--       (b : E → ℝ) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ z : E, |b z| ≤ M) :
--       ∀ (t : ℝ) (q : E),
--         legendre φ q - ((|t| * M : ℝ) : EReal) ≤
--             legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q ∧
--           legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q ≤
--             legendre φ q + ((|t| * M : ℝ) : EReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/LegendreVariation/Perturbation`](https://prove2.me/theorems/e7c006a8-befd-4287-9bdd-21d766535e08).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Next: [`legendre_bounded_perturbation_finite_curve`](https://prove2.me/theorems/f81ed50e-1e1f-44d9-a9cd-afd086601533).
--
--   [Source excerpt, lines 64–71](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Perturbation.lean#L64-L71) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Perturbation.lean#L62-L113 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Perturbation`, declaration `FunctionalInequalities.Analysis.legendre_bounded_perturbation`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Perturbation

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.legendre_bounded_perturbation_readable
    (φ : E → EReal) (hφ : ProperPotential φ)
    (b : E → ℝ) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ z : E, |b z| ≤ M) :
    ∀ (t : ℝ) (q : E),
      legendre φ q - ((|t| * M : ℝ) : EReal) ≤
          legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q ∧
        legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q ≤
          legendre φ q + ((|t| * M : ℝ) : EReal) := by sorry
