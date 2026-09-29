-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_differentiable_and_boundedOnStrips_rsGlobalIntegral_of_hasIotaMoments
-- name    : LanglandsTunnell.RankinSelberg.differentiable_and_boundedOnStrips_rsGlobalIntegral_of_hasIotaMoments
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/5effeb8f-030e-58b7-8948-53722fffe263
-- title:
--   Entirety and strip-boundedness of the GL₂timesGL₃ global integral
-- statement:
--   Work over $\mathbb{Q}$, with $\mathbb{A}$ the adele ring of $\mathbb{Q}$, write $\mathrm{GL}_n(\mathbb{A})$ for the groups `AdelicGL n (𝓞 ℚ) ℚ` (so `AdelicGL2 (𝓞 ℚ) ℚ` is $\mathrm{GL}_2(\mathbb{A})$) equipped with their Borel structure and the Haar measure `adelicGLHaar`, let $\|\det g\| =$ `detNorm g` be the idele norm of $\det g$ for $g \in \mathrm{GL}_2(\mathbb{A})$, and let `iota (𝓞 ℚ) ℚ` be the map $\mathrm{GL}_2(\mathbb{A}) \to \mathrm{GL}_3(\mathbb{A})$ of the cubic-induction package. Let $\Theta : \mathrm{GL}_3(\mathbb{A}) \to \mathbb{C}$ be continuous and satisfy `HasIotaMoments`, i.e. for every subset of $\mathrm{GL}_2(\mathbb{A})$ that is a fundamental domain for the left action of the image of $\mathrm{GL}_2(\mathbb{Q})$ under `globalPoints` with respect to the Haar measure, and every $N \in \mathbb{N}$, the lower integral over that domain of $\|\Theta(\iota g)\| \cdot (\|\det g\|^{N} + \|\det g\|^{-N})$ is finite. Let $D$ be such a fundamental domain, and let $\varphi : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ be continuous with $\|\varphi(g)\| \le C\,\|\det g\|^{r}$ for all $g$, for some real $C, r$. Then the function
--   $$s \mapsto \int_D \varphi(g)\,\Theta(\iota g)\,\|\det g\|^{\,s - 1/2}\,dg$$
--   (`rsGlobalIntegral D s φ Θ`) is differentiable on all of $\mathbb{C}$, and is bounded on vertical strips in the sense of `BoundedOnStrips`: for all real $a \le b$ there is a constant bounding its norm on $\{a \le \operatorname{Re} s \le b\}$.
--
--   This is the global analytic input for the $\mathrm{GL}_2 \times \mathrm{GL}_3$ Rankin–Selberg integral: under a two-sided moment condition on the $\mathrm{GL}_3$ factor along the embedding $\iota$ and a polynomial bound in $\|\det\|$ on the $\mathrm{GL}_2$ factor, the zeta integral is entire and bounded in vertical strips. It is used in the construction of Rankin–Selberg data attached to cubic base change, namely in the statements producing a fundamental domain and a combination of translates on which the global integral is non-vanishing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_differentiable_and_boundedOnStrips_rsGlobalIntegral_of_hasIotaMoments.lean

import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_HonestLDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.differentiable_and_boundedOnStrips_rsGlobalIntegral_of_hasIotaMoments
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΘc : Continuous Θ) (hΘ : HasIotaMoments Θ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (C r : ℝ) (hφ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ ≤ C * detNorm g ^ r) :
    Differentiable ℂ (fun s : ℂ => rsGlobalIntegral D s φ Θ) ∧
      LanglandsTunnell.LDatum.BoundedOnStrips (fun s : ℂ => rsGlobalIntegral D s φ Θ) := by sorry
