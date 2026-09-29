-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_hasSum_torus_radicalCoefficient_mirabolicSeries
-- name    : LanglandsTunnell.CubicInduction.hasSum_torus_radicalCoefficient_mirabolicSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/bfc6bafa-6874-5526-aae0-542401f3bc8e
-- title:
--   Torus sum as radical coefficient of the mirabolic series
-- statement:
--   Let $\mathbb{A}$ denote the adele ring of $\mathbb{Q}$, equipped with its Borel measurable structure. Fix an additive character $\psi : \mathbb{A} \to \mathbb{C}^\times$ which is a global additive character, i.e. trivial on the principal adeles $\psi(\iota(\alpha)) = 1$ for all $\alpha \in \mathbb{Q}$, continuous, and non-trivial, and a function $W$ on $\mathrm{GL}_3(\mathbb{A})$ with complex values which is a $\psi$-Whittaker function in the sense that $W(u(x,y,z)\,g) = \psi(x+y)\,W(g)$ for all $x,y,z \in \mathbb{A}$ and all $g$, where $u(x,y,z)$ is the upper unitriangular matrix with entries $x$ in position $(1,2)$, $y$ in $(2,3)$ and $z$ in $(1,3)$. Assume further that for every $g \in \mathrm{GL}_3(\mathbb{A})$ the family $i \mapsto W(\gamma_i\, g)$, indexed by the classes $i$ of the quotient of $\mathrm{GL}_2(\mathbb{Q})$ by the right relation attached to the image of the homomorphism `unipotentGL2Hom` (the upper unitriangular subgroup of $\mathrm{GL}_2(\mathbb{Q})$), is summable; here $\gamma_i =$ `mirabolicTranslate i` is the element of $\mathrm{GL}_3(\mathbb{A})$ obtained from the chosen representative of $i$ in $\mathrm{GL}_2(\mathbb{Q})$ by passing to $\mathrm{GL}_2(\mathbb{A})$ through `globalPoints` and then applying the embedding `iota`. Then for every $h \in \mathrm{GL}_3(\mathbb{A})$ the family indexed by $\alpha \in \mathbb{Q}^\times$ of the values $W\big(\iota(\mathrm{diag}(\alpha,1))\,h\big)$, where $\mathrm{diag}(\alpha,1) \in \mathrm{GL}_2(\mathbb{A})$ is the diagonal matrix with the image of $\alpha$ in the first entry and $1$ in the second and $\iota$ is the block embedding `iotaGL` sending $M \in \mathrm{GL}_2$ to the $3\times 3$ matrix with block $M$ in the upper left corner and $1$ in position $(3,3)$, is summable with sum $$\int_{\mathbb{A}} \int_{\mathbb{A}} \Big( \sum_{i} W\big(\gamma_i\, r(z,y)\, h\big)\Big)\, \psi(-y)\, d\nu(y)\, d\nu(z),$$ where $r(z,y) = u(0,y,z)$ lies in the unipotent radical of the $(2,1)$ parabolic and $\nu$ is the additive Haar measure of $\mathbb{A}$ conditioned to the adelic box consisting of those adeles whose archimedean component lies in the infinite box and whose finite component is an integral finite adele; the inner integral is taken in $y$ and the outer in $z$.
--
--   This is the expansion, along the unipotent radical of the first maximal parabolic of $\mathrm{GL}_3$, of the series attached to a Whittaker function summed over $N_2(\mathbb{Q})\backslash \mathrm{GL}_2(\mathbb{Q})$, in the form used by Jacquet, Piatetski-Shapiro and Shalika: only the classes of $\mathrm{diag}(\alpha,1)$ survive the two adelic integrations against $\psi(-y)$. It feeds the converse-theorem step of the cubic induction, being used in the construction of the $\mathrm{GL}_3$ automorphy datum and in the functional-equation identity for the associated global zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_hasSum_torus_radicalCoefficient_mirabolicSeries.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction
attribute [local instance] NumberField.AdelicHaar.adeleBorel in

theorem LanglandsTunnell.CubicInduction.hasSum_torus_radicalCoefficient_mirabolicSeries
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hsum : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Summable fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g))
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    HasSum (fun α : ℚˣ => W (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α)) * h))
      (∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
          (∑' i : MirabolicIndex ℚ, W (mirabolicTranslate i * (radicalP21 ![z, y] * h))) * ψ (-y)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) := by sorry
