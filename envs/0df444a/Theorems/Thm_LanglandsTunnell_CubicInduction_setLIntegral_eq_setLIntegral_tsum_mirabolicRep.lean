-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_setLIntegral_eq_setLIntegral_tsum_mirabolicRep
-- name    : LanglandsTunnell.CubicInduction.setLIntegral_eq_setLIntegral_tsum_mirabolicRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/c71c2ad0-dc01-58a0-9fa4-ae97600c5a5b
-- title:
--   Unfolding N(ℚ)-invariant integrals along NbackslashGL₂(ℚ)
-- statement:
--   Work in $G=\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, the general linear group of degree $2$ over the adele ring of $\mathbb{Q}$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`. Inside $G$ sit two subgroups: the range of `globalPoints`, the image of $\mathrm{GL}_2(\mathbb{Q})$ under the map induced by the structure map $\mathbb{Q}\to\mathbb{A}_\mathbb{Q}$, and the range of its composite with `unipotentGL2Hom`, namely the image of the rational upper unipotent matrices $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $x\in\mathbb{Q}$. Let $D_\Gamma, D_N\subseteq G$ be measurable sets assumed to be fundamental domains, for the Haar measure, for the left translation action of the first and of the second of these subgroups respectively. The conclusion asserts: for every measurable $h\colon G\to[0,\infty]$ such that $h(u(x)g)=h(g)$ for all $x\in\mathbb{Q}$ and all $g\in G$, the lower Lebesgue integral of $h$ over $D_N$ equals the integral over $D_\Gamma$ of $g\mapsto\sum_{i} h(\gamma_i g)$, the sum being over the index set `MirabolicIndex ℚ`, the quotient of $\mathrm{GL}_2(\mathbb{Q})$ by the right-coset relation of the rational unipotent subgroup, and $\gamma_i=$ `mirabolicRep ℚ i` the canonical chosen representative of the class $i$.
--
--   This is the unfolding identity for the covering $N(\mathbb{Q})\backslash G\to \mathrm{GL}_2(\mathbb{Q})\backslash G$, written on fundamental domains: translating a fundamental domain for $\mathrm{GL}_2(\mathbb{Q})$ by a set of representatives of $N(\mathbb{Q})\backslash\mathrm{GL}_2(\mathbb{Q})$ produces one for $N(\mathbb{Q})$, and an $N(\mathbb{Q})$-invariant nonnegative function has the same integral over either. It is used in the Rankin–Selberg computations of the Langlands–Tunnell part, where global integrals are unfolded into Whittaker coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_setLIntegral_eq_setLIntegral_tsum_mirabolicRep.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open LanglandsTunnell.CubicInduction

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem LanglandsTunnell.CubicInduction.setLIntegral_eq_setLIntegral_tsum_mirabolicRep
    (DΓ DN : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hDΓ : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range DΓ (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (hDN : IsFundamentalDomain ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range DN
      (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)) :
    ∀ h : AdelicGL2 (𝓞 ℚ) ℚ → ENNReal, Measurable h →
      (∀ (x : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), h (globalPoints (𝓞 ℚ) ℚ (unipotentGL2 x) * g) = h g) →
      ∫⁻ g in DN, h g ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
        ∫⁻ g in DΓ, ∑' i : MirabolicIndex ℚ, h (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i) * g)
          ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by sorry
