-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_bounded_perturbation_finite_curve_readable
-- name    : FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:33.768881+00:00
-- url     : https://prove2.me/theorems/f81ed50e-1e1f-44d9-a9cd-afd086601533
-- title:
--   Finite Legendre Curve Under Bounded Perturbations
-- statement:
--   This gives a finite real-valued perturbation curve for the Legendre transform.
--
--   Let $\phi:E\to\overline{\mathbb R}$ be proper and let $y\in E$ satisfy $\operatorname{Leg}(\phi)(y)\neq+\infty$. Let $b:E\to\mathbb R$, let $M\geq0$, and assume $|b(z)|\leq M$ for every $z$. For every $t\in\mathbb R$, define
--
--   $$
--   \psi_t=\operatorname{Leg}(z\mapsto\phi(z)+t b(z))(y).
--   $$
--
--   Then $\psi_t$ is neither $+\infty$ nor $-\infty$, and
--
--   $$
--   \left|\operatorname{toReal}(\psi_t)-\operatorname{toReal}(\operatorname{Leg}(\phi)(y))\right|
--   \leq |t|M.
--   $$
--
--   This is the finite-value consequence of the extended-real perturbation estimate and is useful for treating Legendre variations as real curves.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem legendre_bounded_perturbation_finite_curve
--       {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       (φ : E → EReal) (hφ : ProperPotential φ) (y : E)
--       (hy : legendre φ y ≠ ⊤)
--       (b : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
--       (hb : ∀ z : E, |b z| ≤ M) :
--       ∀ t : ℝ,
--         let ψ := legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y
--         ψ ≠ ⊤ ∧ ψ ≠ ⊥ ∧
--           |ψ.toReal - (legendre φ y).toReal| ≤ |t| * M
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/LegendreVariation/Perturbation`](https://prove2.me/theorems/e7c006a8-befd-4287-9bdd-21d766535e08).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`legendre_bounded_perturbation`](https://prove2.me/theorems/e3dacbfa-f2d9-4678-b1ae-2ca5c68e3e32).
--
--   Previous: [`legendre_bounded_perturbation`](https://prove2.me/theorems/e3dacbfa-f2d9-4678-b1ae-2ca5c68e3e32).
--
--   [Source excerpt, lines 127–136](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Perturbation.lean#L127-L136) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Perturbation.lean#L125-L185 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Perturbation`, declaration `FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Perturbation

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve_readable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : E → EReal) (hφ : ProperPotential φ) (y : E)
    (hy : legendre φ y ≠ ⊤)
    (b : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ z : E, |b z| ≤ M) :
    ∀ t : ℝ,
      let ψ := legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y
      ψ ≠ ⊤ ∧ ψ ≠ ⊥ ∧
        |ψ.toReal - (legendre φ y).toReal| ≤ |t| * M := by sorry
