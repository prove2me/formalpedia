-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual
-- name    : LanglandsTunnell.CubicInduction.box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/150e4116-ec5c-540b-827a-5de7d89a7228
-- title:
--   Radical Fourier coefficient of the dual mirabolic GL₃ series
-- statement:
--   Work over the adele ring $\mathbb A$ of $\mathbb Q$, equipped with its Borel $\sigma$-algebra and the additive Haar measure `adelicAddHaar`, and let $B$ be the adelic box, the set of adeles whose infinite component lies in the fundamental domain of the lattice basis of the mixed space and whose finite component is everywhere integral. Let $\psi$ be an additive character of $\mathbb A$ with values in $\mathbb C$ which is continuous, nontrivial and trivial on the image of $\mathbb Q$; let $W : \mathrm{GL}_3(\mathbb A) \to \mathbb C$ be continuous and satisfy $W(u(x,y,z)\,h) = \psi(x+y)W(h)$ for every upper unipotent $u(x,y,z)$ (entries $x$, $y$, $z$ in positions $(1,2)$, $(2,3)$, $(1,3)$) and every $h$. Write $\widetilde W(h) = W(w_3\,{}^t h^{-1})$ with $w_3$ the antidiagonal permutation matrix, and assume that for every $h \in \mathrm{GL}_3(\mathbb A)$ the family $i \mapsto \widetilde W(\iota(\gamma_i)h)$ is summable, where $i$ runs over the classes of $\mathrm{GL}_2(\mathbb Q)$ modulo right cosets of the upper unipotent subgroup, $\gamma_i$ is a chosen representative and $\iota$ is the upper-left block embedding of $\mathrm{GL}_2$ into $\mathrm{GL}_3$ composed with the map induced by $\mathbb Q \to \mathbb A$. Fix $g \in \mathrm{GL}_3(\mathbb A)$ and $a \in \mathbb A^\times$, and assume the finiteness hypothesis that $$\sum_{\alpha \in \mathbb Q^\times} \int_{\mathbb A} \bigl\|\widetilde W\bigl(\iota(\mathrm{diag}(\alpha a^{-1},1))\,u_{21}(x)\,w'\,{}^t g^{-1}\bigr)\bigr\|\,dx < \infty,$$ with $u_{21}(x)$ the lower unipotent matrix having $x$ in position $(2,1)$ and $w'$ the permutation matrix exchanging the last two coordinates (lower integral of the nonnegative extended-real integrand). Then the volume of $B$ times the double integral, with respect to the probability measures obtained by conditioning `adelicAddHaar` on $B$ in the variables $z$ and $y$, of $$\Bigl(\sum_i \widetilde W\bigl(\iota(\gamma_i)\,w'\,{}^t(r(z,y)\,\iota(\mathrm{diag}(a,1))\,g)^{-1}\bigr)\Bigr)\psi(-y),$$ where $r(z,y)$ is the upper unipotent matrix with $0$, $y$, $z$ in positions $(1,2)$, $(2,3)$, $(1,3)$, equals the idele norm of $a$ (the value of the distributive Haar character of $\mathbb A$ at $a$) times $$\sum_{\alpha \in \mathbb Q^\times} \int_{\mathbb A} \widetilde W\bigl(\iota(\mathrm{diag}(\alpha a^{-1},1))\,u_{21}(x)\,w'\,{}^t g^{-1}\bigr)\,dx.$$
--
--   This is the unfolding step identifying the Fourier coefficient, against $\psi(-y)$, of the dual mirabolic Whittaker series along the radical of the $(2,1)$-parabolic with the inner integral of the dual $\mathrm{GL}_3 \times \mathrm{GL}_1$ zeta integral, the averaging over the box serving to extract the coefficient. It feeds the construction of the functional equation relating the global zeta integral and its dual in the cubic induction step of the converse-theorem argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem LanglandsTunnell.CubicInduction.box_integral_dualSeries_radical_eq_ideleNorm_mul_tsum_integral_dual
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hWc : Continuous W) (_hW : IsGL3PsiWhittakerFn ψ W)
    (_hsum' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      Summable fun i : MirabolicIndex ℚ => dualWhittakerFn3 W (mirabolicTranslate i * g))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (_hfin : (∑' α : ℚˣ, ∫⁻ x : AdeleRing (𝓞 ℚ) ℚ,
        (‖dualWhittakerFn3 W (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α * a⁻¹)) *
            lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))‖₊ : ENNReal)
          ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) < ⊤) :
    ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
      (∫ z : AdeleRing (𝓞 ℚ) ℚ, ∫ y : AdeleRing (𝓞 ℚ) ℚ,
          (∑' i : MirabolicIndex ℚ, dualWhittakerFn3 W (mirabolicTranslate i *
            (weylPrime3 * transposeInv3 (radicalP21 ![z, y] * (iotaGL (diagUnitGL2 a) * g))))) * ψ (-y)
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
        ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) =
    ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) *
      ∑' α : ℚˣ, ∫ x : AdeleRing (𝓞 ℚ) ℚ,
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) α * a⁻¹)) *
          lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))
        ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by sorry
