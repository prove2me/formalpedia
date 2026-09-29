-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_differentiable_rsGlobalIntegral_and_boundedOnStrips_of_hasIotaMoments
-- name    : LanglandsTunnell.RankinSelberg.differentiable_rsGlobalIntegral_and_boundedOnStrips_of_hasIotaMoments
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/4a5f564d-ccf5-51af-8fbe-85920abbc524
-- title:
--   Entirety and strip-boundedness of a GL₂timesGL₃ Rankin–Selberg integral
-- statement:
--   Work over $\mathbb{Q}$, with the groups $\mathrm{GL}_2$ and $\mathrm{GL}_3$ of the adele ring, carrying the Borel $\sigma$-algebra [`NumberField.AdelicHaar.glBorel`](def/NumberField_AdelicHaar.html#L176) and the Haar measure [`NumberField.AdelicHaar.adelicGLHaar`](def/NumberField_AdelicHaar.html#L189). Let $D$ be a subset of $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ which is a fundamental domain, for this Haar measure, for the action of the range of `globalPoints (𝓞 ℚ) ℚ`, that is of the image of $\mathrm{GL}_2(\mathbb{Q})$ under the map induced by $\mathbb{Q}\to\mathbb{A}_\mathbb{Q}$. Let $\varphi:\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ be continuous and such that $\|\varphi(g)\|\,\|\det g\|^{-1/2}$ is bounded above by some real constant, where $\|\det g\|$ is the idele norm `detNorm` of the determinant. Let $\Theta:\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ be continuous and satisfy `HasIotaMoments`: for every such fundamental domain and every $N\in\mathbb{N}$, the lower integral over it of $\|\Theta(\iota g)\|\,(\|\det g\|^{N}+\|\det g\|^{-N})$ is finite, $\iota$ being the map `iota (𝓞 ℚ) ℚ` from $\mathrm{GL}_2$ to $\mathrm{GL}_3$. Then the function $s\mapsto\int_D\varphi(g)\,\Theta(\iota g)\,\|\det g\|^{\,s-1/2}\,dg$ is complex differentiable at every point of $\mathbb{C}$, and satisfies `BoundedOnStrips`: for all reals $a\le b$ there is a constant bounding its norm on $\{a\le\operatorname{Re}s\le b\}$.
--
--   This is the analytic input to the global $\mathrm{GL}_2\times\mathrm{GL}_3$ Rankin–Selberg construction: absolute convergence of two-sided moments of the $\mathrm{GL}_3$ function along the embedding of $\mathrm{GL}_2$ yields entirety of the global integral together with boundedness on vertical strips. It supplies the corresponding two clauses for the Rankin–Selberg $L$-datum used in the comparison of the global integral with the archimedean factor times the $L$-function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_differentiable_rsGlobalIntegral_and_boundedOnStrips_of_hasIotaMoments.lean

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

theorem LanglandsTunnell.RankinSelberg.differentiable_rsGlobalIntegral_and_boundedOnStrips_of_hasIotaMoments
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (hφb : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΘc : Continuous Θ) (hΘ : HasIotaMoments Θ) :
    Differentiable ℂ (fun s : ℂ => rsGlobalIntegral D s φ Θ) ∧
      LanglandsTunnell.LDatum.BoundedOnStrips (fun s : ℂ => rsGlobalIntegral D s φ Θ) := by sorry
