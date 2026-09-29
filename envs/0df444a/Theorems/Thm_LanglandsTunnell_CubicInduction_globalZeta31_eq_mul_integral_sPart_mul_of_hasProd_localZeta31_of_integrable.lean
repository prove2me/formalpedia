-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_globalZeta31_eq_mul_integral_sPart_mul_of_hasProd_localZeta31_of_integrable
-- name    : LanglandsTunnell.CubicInduction.globalZeta31_eq_mul_integral_sPart_mul_of_hasProd_localZeta31_of_integrable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/ee1913af-c72f-5db7-b9d2-83309ef7692d
-- title:
--   Euler factorisation of the unipotent GL₃× GL₁ zeta integral
-- statement:
--   Let $S$ be a finite set of maximal ideals of $\mathbb{Z}$, let $W$ be a complex function on $GL_3$ of the adeles of $\mathbb{Q}$, $W_{\mathrm{arch}}$ a function on $GL_3$ of the infinite adele ring, and $W_{\mathrm{loc},v}$ a function on $GL_3(\mathbb{Q}_v)$ for each finite place $v$. Assume: (`hfac`) for every adelic $x$ and every finite $T\supseteq S$ such that the component of $x$ at each $v\notin T$ lies in `localMaximalCompact3 v` (matrices whose entries and whose inverse's entries all have valuation $\le 1$), $W(x)=W_{\mathrm{arch}}(x_\infty)\prod_{v\in T}W_{\mathrm{loc},v}(x_v)$; (`hK`) for $v\notin S$, $W_{\mathrm{loc},v}$ is right invariant under `localMaximalCompact3 v`; (`hW1`) $W_{\mathrm{loc},v}(1)=1$ for $v\notin S$; (`hint`) for $v\notin S$, $y\mapsto W_{\mathrm{loc},v}(\mathrm{lowerUnipotent21}\,y)$ is integrable for the self-dual Haar measure $\mathrm{d}y$ at $v$; (`hsum`) the excesses $\mathrm{vol}(\mathcal{O}_v)^{-1}\int\|W_{\mathrm{loc},v}(\mathrm{lowerUnipotent21}\,y)\|\,\mathrm{d}y-1$ are summable over $v\notin S$. Let $\chi$ be a homomorphism from the idele units to $\mathbb{C}^\times$ trivial on every unit idele that is $1$ at the infinite component and at all $v\in S$ and whose finite part is integral with integral inverse, and let $g\in GL_3$ of the adeles have components in `localMaximalCompact3 v` for $v\notin S$. Let $\sigma_0\in\mathbb{R}$ and $L:\mathbb{C}\to\mathbb{C}$ be such that for $\operatorname{Re} s>\sigma_0$ the family indexed by $v\notin S$ of the quantities $\mathrm{vol}\{u:|u|_v=1\}^{-1}\,\mathrm{vol}(\mathcal{O}_v)^{-1}\,\mathrm{localZeta31}_v$, formed with the multiplicative measure obtained from the self-dual measure by pulling back $\mathrm{d}^\times x=|x|^{-1}\mathrm{d}x$ along $x\mapsto x$ on units, the self-dual additive measure, $W_{\mathrm{loc},v}$, the $v$-component of $\chi$, and $g=1$, has product $L(s)$. Finally let $H_\nu$ be `ProductMeasureData` for $S$ and the Haar measure of the idele class group, and assume for $\operatorname{Re} s>\sigma_0$ both that the $S$-part integrand appearing in the conclusion is integrable for $H_\nu.\mathrm{\nu S}$ and that $(a,x)\mapsto W(\iota(\mathrm{diag}(a,1))\,\mathrm{lowerUnipotent21}(x)\,g)\chi(a)\|a\|^{s-1}$ is integrable for the product of the idelic and adelic Haar measures. Then, for every $s$ with $\operatorname{Re} s>\sigma_0$, the global zeta integral $\mathrm{globalZeta31}(W,\chi,s,g)$ equals $H_\nu.c$ times the volume of the adelic box times $2^{r_2}/\sqrt{|d_{\mathbb{Q}}|}$ times the integral over the ideles, for $H_\nu.\mathrm{\nu S}$, of the product of the archimedean integral of $W_{\mathrm{arch}}$ along the lower unipotent line, the normalised local integrals at the places of $S$, $\chi(a)$ and $\|a\|^{s-1}$, times $L(s)$.
--
--   This is the unfolding of the global $GL_3\times GL_1$ zeta integral, integrated along the lower unipotent line, into an archimedean factor, a finite $S$-part integral and an Euler product of local zeta integrals over the places outside $S$, with the comparison constant made explicit in terms of the product-measure data, the volume of the adelic box and the discriminant. It is the factorisation step used in the cubic-induction analysis of the relevant $L$-function, feeding the statements that compare the value of the completed product with its root-number-twisted reflection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_globalZeta31_eq_mul_integral_sPart_mul_of_hasProd_localZeta31_of_integrable.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicBox
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  NumberField.InfinitePlace

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in
attribute [local instance] LanglandsTunnell.TateLocal.localBorel in
open scoped Classical in

theorem
LanglandsTunnell.CubicInduction.globalZeta31_eq_mul_integral_sPart_mul_of_hasProd_localZeta31_of_integrable
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (hfac : ∀ (x : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W x = Warch (archComponent3 (𝓞 ℚ) ℚ x) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v x))
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hW1 : ∀ v, v ∉ S → Wloc v 1 = 1)
    (hint : ∀ v, v ∉ S →
      letI := localBorel ℚ v
      Integrable (fun y => Wloc v (lowerUnipotent21 y)) (selfDualHaarAt ℚ v))
    (hsum : Summable fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
      letI := localBorel ℚ v.1
      ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)))⁻¹
          * (∫ y, ‖Wloc v.1 (lowerUnipotent21 y)‖ ∂(selfDualHaarAt ℚ v.1)) - 1)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hχU : ∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 ℚ) ℚ).2 v = 1) →
      NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ →
      χ u = 1)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (σ₀ : ℝ) (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          letI := localBorel ℚ v.1
          ((selfDualHaarAt ℚ v.1).real {u : v.1.adicCompletion ℚ | Valued.v u = 1} : ℂ)⁻¹ *
          ((selfDualHaarAt ℚ v.1).real (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)) : ℂ)⁻¹ *
            localZeta31 v.1 (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v.1)))
              (selfDualHaarAt ℚ v.1) (Wloc v.1) (TateGlobal.localChar χ v.1) s 1)
        (L s))
    (Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ))
    (hS : ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        (∫ y : mixedEmbedding.mixedSpace ℚ,
            Warch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
              lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
          (∏ v ∈ S,
            (letI := localBorel ℚ v
             ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
               ∫ x : v.adicCompletion ℚ,
                 Wloc v (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                   lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                   ∂(selfDualHaarAt ℚ v))) *
          ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
        Hν.νS)
    (hG : ∀ s : ℂ, σ₀ < s.re →
      letI := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
      Integrable (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × AdeleRing (𝓞 ℚ) ℚ =>
        W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g) * ((χ p.1 : ℂˣ) : ℂ) *
          ((TateGlobal.ideleNorm ℚ p.1 : ℝ) : ℂ) ^ (s - 1))
        ((NumberField.Idele.idelicHaar ℚ).prod (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) :
    ∀ s : ℂ, σ₀ < s.re →
      globalZeta31 W χ s g =
        (Hν.c : ℂ) * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) *
          (((2 : ℝ) ^ nrComplexPlaces ℚ / Real.sqrt |(discr ℚ : ℝ)| : ℝ) : ℂ) *
          (∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
            (∫ y : mixedEmbedding.mixedSpace ℚ,
                Warch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                  lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
              (∏ v ∈ S,
                (letI := localBorel ℚ v
                 ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                   ∫ x : v.adicCompletion ℚ,
                     Wloc v (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                       lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                       ∂(selfDualHaarAt ℚ v))) *
              ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
            ∂Hν.νS) *
          L s := by sorry
