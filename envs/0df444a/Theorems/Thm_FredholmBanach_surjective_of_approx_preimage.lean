-- Prove2me | Theorems.Thm_FredholmBanach_surjective_of_approx_preimage
-- name    : FredholmBanach.surjective_of_approx_preimage
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T23:05:12.131449+00:00
-- url     : https://prove2.me/theorems/d037a612-8cd9-4e67-887e-6c5974b61ecd
-- title:
--   Approximate solvability with norm control implies surjectivity
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $X$ be a Banach space and $Y$ a normed space over $\mathbb{K}$, and let $f:X\to Y$ be a bounded linear map. Suppose there is a constant $C$ such that for every $y\in Y$ with $\|y\|\le 1$ there exists $x\in X$ with $\|x\|\le C$ and $\|f(x)-y\|\le \tfrac12$. Then $f$ is surjective.
--
--   This criterion deduces exact surjectivity from approximate solvability with norm control, without completeness of the target space. It is reusable for showing that a perturbed operator, possibly enlarged by a finite-dimensional summand, is onto.
--
--   **Formalization Note.** $\mathbb{K}$ is an `RCLike` field, $X$ is a complete normed space and $Y$ a normed space over it, and $f$ is `f : X →L[𝕜] Y`. The constant `C : ℝ` is arbitrary (no sign assumption). Surjectivity is `Function.Surjective f`.
-- source:
--   Auxiliary statement for N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 5, n° 2, Théorème 2, p. TS III.73

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

/-- A bounded linear map `f` from a Banach space `X` to a normed space `Y` is surjective as soon
as every vector `y` of norm at most `1` lies within distance `1 / 2` of the image under `f` of
the closed ball of some fixed radius `C`. -/
theorem surjective_of_approx_preimage {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) {C : ℝ} (hf : ∀ y : Y, ‖y‖ ≤ 1 → ∃ x, ‖x‖ ≤ C ∧ ‖f x - y‖ ≤ 1 / 2) :
    Function.Surjective f := by sorry

end FredholmBanach
