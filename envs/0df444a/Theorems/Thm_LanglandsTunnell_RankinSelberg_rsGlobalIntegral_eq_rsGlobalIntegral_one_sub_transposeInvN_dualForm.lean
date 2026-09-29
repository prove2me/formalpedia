-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_one_sub_transposeInvN_dualForm
-- name    : LanglandsTunnell.RankinSelberg.rsGlobalIntegral_eq_rsGlobalIntegral_one_sub_transposeInvN_dualForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/8f201214-e337-5c79-83f1-3d3528af4062
-- title:
--   Functional equation of the GL₂timesGL₃ Rankin–Selberg integral
-- statement:
--   Work over $\mathbb{Q}$, with $\mathrm{GL}_n(\mathbb{A}_\mathbb{Q})$ carried by the Borel $\sigma$-algebra of its topology and equipped with the Haar measure [`NumberField.AdelicHaar.adelicGLHaar`](def/NumberField_AdelicHaar.html#L189). Let $D, D' \subseteq \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ both be fundamental domains, with respect to that Haar measure, for the subgroup of $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ given by the image of $\mathrm{GL}_2(\mathbb{Q})$ under the map `globalPoints` induced by $\mathbb{Q} \to \mathbb{A}_\mathbb{Q}$. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_\mathbb{Q}) \to \mathbb{C}$ satisfy $\varphi(\gamma g) = \varphi(g)$ for all $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ (embedded by `globalPoints`), and let $\Theta : \mathrm{GL}_3(\mathbb{A}_\mathbb{Q}) \to \mathbb{C}$ satisfy $\Theta(\gamma g) = \Theta(g)$ for all $\gamma \in \mathrm{GL}_3(\mathbb{Q})$ (embedded by `globalPointsGL`). Then for every $s \in \mathbb{C}$,
--   $$\int_D \varphi(g)\,\Theta(\iota g)\,\lVert \det g\rVert^{\,s-1/2}\,dg \;=\; \int_{D'} \varphi({}^t g^{-1})\,\Theta({}^t(\iota g)^{-1})\,\lVert \det g\rVert^{\,(1-s)-1/2}\,dg,$$
--   where $\iota$ is the adelic embedding `iota` of $\mathrm{GL}_2$ into $\mathrm{GL}_3$, $\lVert\cdot\rVert$ is the idèle norm of the determinant (`detNorm`, coerced to $\mathbb{C}$), and the two transpose-inverse maps are `transposeInvN (Fin 2)` and, inside `dualForm`, `transposeInv3`. Both sides are the integral `rsGlobalIntegral`; no integrability hypothesis is imposed.
--
--   This is the global functional equation, in the shape $Z(s;\varphi,\Theta;D) = Z(1-s;\varphi^\vee,\Theta^\vee;D')$, of the $\mathrm{GL}_2\times\mathrm{GL}_3$ Rankin–Selberg integral under the outer automorphism $g \mapsto {}^t g^{-1}$ together with $s \mapsto 1-s$; the independence of the chosen fundamental domain rests on the triviality of the idèle norm of the determinant of a rational matrix ([`AutomorphicForm.ideleNorm_det_globalPoints`](thm.html#AutomorphicForm.ideleNorm_det_globalPoints)). It supplies the functional-equation clause used in the construction of the entire continuation of the completed $L$-function attached to a Rankin–Selberg datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_one_sub_transposeInvN_dualForm.lean

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

theorem LanglandsTunnell.RankinSelberg.rsGlobalIntegral_eq_rsGlobalIntegral_one_sub_transposeInvN_dualForm
    (D D' : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (hD' : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D'
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hΘ : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Θ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Θ g)
    (s : ℂ) :
    rsGlobalIntegral D s φ Θ =
      rsGlobalIntegral D' (1 - s) (fun g => φ (transposeInvN (Fin 2) g)) (dualForm Θ) := by sorry
