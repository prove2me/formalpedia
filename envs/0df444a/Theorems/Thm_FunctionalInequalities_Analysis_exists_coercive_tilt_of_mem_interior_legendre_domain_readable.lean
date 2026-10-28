-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_coercive_tilt_of_mem_interior_legendre_domain_readable
-- name    : FunctionalInequalities.Analysis.exists_coercive_tilt_of_mem_interior_legendre_domain_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:07.968648+00:00
-- url     : https://prove2.me/theorems/2a6ee0ab-9933-4999-9219-7fdf5606d335
-- title:
--   Linear Coercivity of an Interior Legendre Tilt
-- statement:
--   This is a pointwise coercivity result for a proper extended-real potential.
--
--   Let $E$ be a finite-dimensional real inner-product normed space, let $\phi:E\to\overline{\mathbb R}$ be a `ProperPotential`, and let $y$ lie in the interior of the finite domain
--   $$\{q:E\mid \operatorname{legendre}(\phi)(q)\ne+\infty\}.$$
--
--   Then there exist real numbers $a,b$ with $a>0$ such that, for every $z\in E$,
--   $$\bigl(a\|z\|-b\bigr)\le \phi(z)-\langle z,y\rangle,$$
--   where the real affine expression is embedded into `EReal` and the inner product is likewise coerced.
--
--   No convexity, differentiability, nonnegativity, or global finiteness of $\phi$ is assumed. The result supplies the linear decay needed to establish attainment of a Legendre supremum.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_coercive_tilt_of_mem_interior_legendre_domain
--       (φ : E → EReal) (hφ : ProperPotential φ) (y : E)
--       (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤}) :
--       ∃ (a b : ℝ), 0 < a ∧ ∀ z : E,
--         ((a * ‖z‖ - b : ℝ) : EReal) ≤ φ z - (inner ℝ z y : EReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/LegendreVariation/Attainment`](https://prove2.me/theorems/8fff00c5-0262-4f99-9cab-27221baba48b).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`affineMaximum_coercive`](https://prove2.me/theorems/e32066d6-367b-466d-9089-f5d72ac05f70).
--
--   Previous: [`conjugate_maximizer_eq_gradient`](https://prove2.me/theorems/80335e95-bd3b-41ae-b542-89eb54c17879) · Next: [`tiltedObjective_data`](https://prove2.me/theorems/e3e2f5b2-8368-425f-a963-03a46f5caf8c).
--
--   [Source excerpt, lines 210–214](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean#L210-L214) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean#L207-L275 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment`, declaration `FunctionalInequalities.Analysis.exists_coercive_tilt_of_mem_interior_legendre_domain`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Attainment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.exists_coercive_tilt_of_mem_interior_legendre_domain_readable
    (φ : E → EReal) (hφ : ProperPotential φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤}) :
    ∃ (a b : ℝ), 0 < a ∧ ∀ z : E,
      ((a * ‖z‖ - b : ℝ) : EReal) ≤ φ z - (inner ℝ z y : EReal) := by sorry
