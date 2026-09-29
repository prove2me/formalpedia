-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage
-- name    : LanglandsTunnell.RankinSelberg.rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/e1c5a710-dfe5-5b71-845a-a6ca3440a721
-- title:
--   Transpose–inverse invariance of the GL₂timesGL₃ Rankin–Selberg integral
-- statement:
--   Let $\mathbb{A}$ denote the adele ring of $\mathbb{Q}$ (the adeles of the Dedekind domain $\mathcal{O}_{\mathbb{Q}}$ with fraction field $\mathbb{Q}$), let $\theta =$ `transposeInvN (Fin 2)` be the map sending $g \in \mathrm{GL}_2(\mathbb{A})$ to the transpose of $g^{-1}$, and equip $\mathrm{GL}_2(\mathbb{A})$ with the Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`. For an arbitrary subset $D \subseteq \mathrm{GL}_2(\mathbb{A})$, two assertions are made. First, for every $s \in \mathbb{C}$, every $\varphi \colon \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ and every $\Theta \colon \mathrm{GL}_3(\mathbb{A}) \to \mathbb{C}$, the Bochner integral $\int_D \varphi(g)\,\Theta(\iota g)\,\lVert \det g\rVert^{\,s-1/2}\,dg$, where $\iota$ is the embedding `iota` of $\mathrm{GL}_2$ into $\mathrm{GL}_3$ and $\lVert \det g \rVert$ is the idele norm of $\det g$, equals the corresponding integral formed from the data $\theta^{-1}(D)$, $1-s$, $\varphi \circ \theta$ and $\Theta^\vee$, where $\Theta^\vee(x) = \Theta({}^t x^{-1})$ is `dualForm`; in particular the identity holds unconditionally, with both sides equal to $0$ off the region of integrability. Second, if $D$ is a fundamental domain, with respect to `adelicGLHaar`, for the subgroup of $\mathrm{GL}_2(\mathbb{A})$ that is the range of the map `globalPoints` induced by $\mathbb{Q} \to \mathbb{A}$ on $\mathrm{GL}_2$, then so is $\theta^{-1}(D)$.
--
--   This is the involution step underlying the functional equation of the global Rankin–Selberg integral of a form on $\mathrm{GL}_2$ against a form on $\mathrm{GL}_3$: the substitution $g \mapsto {}^t g^{-1}$ exchanges $s$ and $1-s$ and replaces the $\mathrm{GL}_3$ datum by its dual, while transporting fundamental domains for the rational points. It feeds the construction of a fundamental domain together with the values of the Rankin–Selberg integrals on a finite family of archimedean realisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage.lean

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

theorem LanglandsTunnell.RankinSelberg.rsGlobalIntegral_eq_rsGlobalIntegral_transposeInvN_dualForm_and_isFundamentalDomain_preimage
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :
    (∀ (s : ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      rsGlobalIntegral D s φ Θ =
        rsGlobalIntegral (transposeInvN (Fin 2) ⁻¹' D) (1 - s)
          (fun g => φ (transposeInvN (Fin 2) g)) (dualForm Θ)) ∧
    (IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
        (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) →
      IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range (transposeInvN (Fin 2) ⁻¹' D)
        (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)) := by sorry
