-- Prove2me | Theorems.Thm_LanglandsTunnell_isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm
-- name    : LanglandsTunnell.isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/23504abf-a05e-52fc-8112-7496abe8db6f
-- title:
--   Archimedean derivatives and Casimir commute with Whittaker integration
-- statement:
--   Fix data $D \subseteq \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, an assignment $U$ of a subgroup of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ to each ideal of $\mathbb{Z} = \mathcal{O}_{\mathbb{Q}}$, and an assignment $\mathrm{gen}$ of an element of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ to each finite place; let $\psi$ be a continuous additive character of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, let $w$ be an infinite place of $\mathbb{Q}$ together with a proof $hw$ that $w$ is real, let $\varphi : \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$, and let $\alpha \in \mathbb{Q}$. Assume `IsArchSmoothAt hw φ`: for every $g$ the function $e \mapsto \varphi(g \cdot \mathrm{archRealLiftAt}\,hw\,e)$ on real $2 \times 2$ matrices is $C^{\infty}$ on the locus $\det e \neq 0$, where the lift inserts $e$ at the real place $w$; and assume `IsKfSmooth ℚ φ`: the stabiliser of $\varphi$ for right translation by the subgroup of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ that is the kernel of the archimedean projection is an open subgroup. Write $\mathrm{pins} = \mathrm{productionPinsOf}\ \mathbb{Q}\ D\ U\ \mathrm{gen}\ (\mathrm{adelicBox}\ \mathbb{Q})$, the package carrying the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, the data $D$, $Z = \top$, $U$, $\mathrm{gen}$, the Borel structure on $\mathbb{A}_{\mathbb{Q}}$ and the measure $\nu$ obtained from adelic additive Haar measure by conditioning on the box $\mathrm{adelicBox}\ \mathbb{Q}$ (infinite part in a fundamental domain for the Minkowski lattice, finite part integral at every place), and let $$W(g) = \int \varphi(n(x)\,g)\,\psi(-(\alpha x))\,d\nu(x), \qquad n(x) = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix},$$ be `whittakerCoefficient ℚ pins ψ φ α`. The conclusion is threefold: $W$ again satisfies `IsArchSmoothAt hw`; for each of the three directions $d \in \{H, E, F\}$ the derivative $\mathrm{archDerivAt}\,hw\,d$, namely differentiation at $t = 0$ along the one-parameter flow $g \mapsto g \cdot \mathrm{archFlowAt}\,hw\,d\,t$ at the real place, satisfies $\mathrm{archDerivAt}\,hw\,d\,W = \mathrm{whittakerCoefficient}\ \mathbb{Q}\ \mathrm{pins}\ \psi\ (\mathrm{archDerivAt}\,hw\,d\,\varphi)\ \alpha$; and the same holds for the Casimir operator $\mathrm{archCasimirAt}\,hw = -\bigl(\tfrac14 H^2 - \tfrac12 H + EF\bigr)$ built from these derivatives.
--
--   This is the statement that Whittaker–Fourier integration in the unipotent variable commutes with the archimedean Lie-algebra action: differentiation under the integral sign for the three standard directions of $\mathfrak{gl}_2(\mathbb{R})$ and hence for the Casimir element, together with preservation of archimedean smoothness. It is used where Whittaker coefficients of a function with prescribed Casimir eigenvalue are analysed through the resulting ordinary differential equation on the torus, and in the Langlands–Tunnell part of the development where archimedean types of Whittaker coefficients over $\mathbb{Q}$ are identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicBox

theorem LanglandsTunnell.isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (w : InfinitePlace ℚ) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hsm : IsArchSmoothAt hw φ) (hKf : IsKfSmooth ℚ φ) (α : ℚ) :
    IsArchSmoothAt hw (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α) ∧
      (∀ d : ArchDir,
        archDerivAt hw d (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α)
          = whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ (archDerivAt hw d φ) α) ∧
      archCasimirAt hw (whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α)
        = whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ (archCasimirAt hw φ) α := by sorry
