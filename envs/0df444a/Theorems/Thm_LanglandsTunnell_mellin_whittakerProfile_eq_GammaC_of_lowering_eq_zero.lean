-- Prove2me | Theorems.Thm_LanglandsTunnell_mellin_whittakerProfile_eq_GammaC_of_lowering_eq_zero
-- name    : LanglandsTunnell.mellin_whittakerProfile_eq_GammaC_of_lowering_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/79f4cde3-befa-5ee3-983f-57a8da31ac16
-- title:
--   Mellin transform of a lowering-annihilated Whittaker profile is Γ_ℂ
-- statement:
--   Let $e \in \mathbb{C}$, let $k_0 \in \mathbb{Z}$, let $W : \mathbb{C} \to \mathbb{C}$, and let $f_{+}, f_{-} : \mathbb{R} \to \mathbb{C}$ be such that $W(t) = (\sqrt{t})^{\,e+1} f_{+}(t)$ and $W(-t) = (\sqrt{t})^{\,e+1} f_{-}(t)$ for every real $t > 0$ (the power being the complex power of the positive real $\sqrt{t}$). Assume $f_{+}$ and $f_{-}$ are differentiable on $(0,\infty)$ and satisfy there the first-order equations $2y f_{+}'(y) + (4\pi y - k_0) f_{+}(y) = 0$ and $2y f_{-}'(y) - (4\pi y + k_0) f_{-}(y) = 0$ for all $y > 0$; assume $f_{-}$ has at most polynomial growth, i.e. there are reals $C, N$ with $\lVert f_{-}(y)\rVert \le C y^{N}$ for all $y \ge 1$; and assume $f_{+}(y) \ne 0$ for some $y > 0$. Then $W(t) = 0$ for every real $t < 0$, and there exists $\rho \in \mathbb{C}$, $\rho \ne 0$, such that for every $b \in \mathbb{Z}/2$ and every $s \in \mathbb{C}$ with $\operatorname{Re} s > -\operatorname{Re}(e/2 + (k_0-1)/2)$ the function $t \mapsto (\rho W(t) + (-1)^{b} \rho W(-t))/t$ is Mellin convergent at $s$, with Mellin transform $\int_0^{\infty} t^{s-1} (\rho W(t) + (-1)^{b}\rho W(-t))\,t^{-1}\,dt = \Gamma_{\mathbb{C}}\bigl(s + e/2 + (k_0-1)/2\bigr)$, where $\Gamma_{\mathbb{C}}(z) = 2(2\pi)^{-z}\Gamma(z)$. Since $W$ vanishes on the negative reals and the Mellin integral is over $(0,\infty)$, the value does not in fact depend on $b$.
--
--   This is the archimedean computation for $\mathrm{GL}(2,\mathbb{R})$: a Whittaker function whose restriction to the split torus is annihilated by the lowering operator in weight $k_0$ is, up to a scalar, $y^{k_0/2}e^{-2\pi y}$ on the positive ray and zero on the negative ray, so that after normalisation its Mellin transform is exactly the complex Gamma factor $\Gamma_{\mathbb{C}}$. It feeds the lemmas producing Whittaker factorisations for archimedean Casimir eigenvectors of minimal weight, and thence the archimedean datum attached to weight-one forms in the cubic-induction step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_mellin_whittakerProfile_eq_GammaC_of_lowering_eq_zero.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.mellin_whittakerProfile_eq_GammaC_of_lowering_eq_zero (e : ℂ) (k₀ : ℤ) (W : ℂ → ℂ)
    (fp fm : ℝ → ℂ)
    (hWp : ∀ t : ℝ, 0 < t → W t = ((Real.sqrt t : ℝ) : ℂ) ^ (e + 1) * fp t)
    (hWm : ∀ t : ℝ, 0 < t → W (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (e + 1) * fm t)
    (hfp : DifferentiableOn ℝ fp (Set.Ioi 0)) (hfm : DifferentiableOn ℝ fm (Set.Ioi 0))
    (hlowp : ∀ y : ℝ, 0 < y →
      2 * (y : ℂ) * deriv fp y + (4 * (π : ℂ) * (y : ℂ) - (k₀ : ℂ)) * fp y = 0)
    (hlowm : ∀ y : ℝ, 0 < y →
      2 * (y : ℂ) * deriv fm y - (4 * (π : ℂ) * (y : ℂ) + (k₀ : ℂ)) * fm y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖fm y‖ ≤ C * y ^ N)
    (hne : ∃ y : ℝ, 0 < y ∧ fp y ≠ 0) :
    (∀ t : ℝ, t < 0 → W t = 0) ∧
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (b : ZMod 2) (s : ℂ), -(e / 2 + ((k₀ : ℂ) - 1) / 2).re < s.re →
      MellinConvergent (fun t : ℝ => (ρ * W t + (-1 : ℂ) ^ b.val * (ρ * W (-t))) / (t : ℂ)) s ∧
        mellin (fun t : ℝ => (ρ * W t + (-1 : ℂ) ^ b.val * (ρ * W (-t))) / (t : ℂ)) s
          = Complex.Gammaℂ (s + (e / 2 + ((k₀ : ℂ) - 1) / 2)) := by sorry
