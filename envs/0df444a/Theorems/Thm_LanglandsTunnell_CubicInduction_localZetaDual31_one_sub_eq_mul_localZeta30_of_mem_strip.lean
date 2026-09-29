-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip
-- name    : LanglandsTunnell.CubicInduction.localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/e6c332cd-44e4-56fd-be13-28e232c70e20
-- title:
--   Local functional equation for the GL₃ zeta integrals
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and let $\nu_0,\nu_1,\nu_2$ be locally constant characters $(\mathbb{Q}_v)^{\times}\to\mathbb{C}^{\times}$, let $\Phi$ be a locally constant, compactly supported function on $\mathbb{Q}_v^3$, and let $\chi$ be a locally constant character of $(\mathbb{Q}_v)^{\times}$ such that each $\nu_i\chi$ has absolute value $1$ at the uniformizer unit, and such that $\nu_i\chi$ is trivial on the $a_i$-th higher unit group while for every $m<a_i$ some unit in the $m$-th higher unit group is not fixed, i.e. $a_i$ is the conductor exponent of $\nu_i\chi$. Put $W(h)=\mathrm{jacquetWhittaker3}\,v\,\nu\,\Phi\,(h\cdot w_0)$, the Jacquet–Whittaker function of the cell section attached to $(\nu,\Phi)$ right-translated by the antidiagonal matrix $w_0=$ `antidiagonal3 v`. Write $\mu$ for the multiplicative measure $|x|^{-1}\,d x$ on $\mathbb{Q}_v^{\times}$ obtained from the self-dual additive Haar measure, pulled back along the inclusion of units. Assume: for every $s$ with $\sigma_0<\operatorname{re}s$ the function $a\mapsto W(\iota(\operatorname{diag}(a))) \chi(a)|a|^{s-1}$ is $\mu$-integrable; and for every $s$ with $\sigma_1<\operatorname{re}s$ the function $(a,x)\mapsto W(w_{\mathrm{long}}\,{}^{t}(\iota(\operatorname{diag}(a))\,u^{-}(x)\,w'\,{}^{t}1)^{-1})\,\chi^{-1}(a)|a|^{s-1}$ is integrable for $\mu$ times the self-dual measure, where $w'=$ `weylPrime3` and ${}^{t}(\cdot)^{-1}$ is `transposeInv3`. Then for every $s$ with $\sigma_0<\operatorname{re}s$, $\sigma_1<\operatorname{re}(1-s)$ and $0<\operatorname{re}s<1$, the dual zeta integral $\mathrm{localZetaDual31}$ of $W$ against $\chi$ at $1-s$ and the identity equals $$\Big(\prod_i L_v((\nu_i\chi)^{-1},1-s)\Big)\Big(\prod_i\varepsilon_v(\nu_i\chi)\Big)\,(\mathrm{N}v)^{(\sum_i a_i)(1/2-s)}\Big(\prod_i L_v(\nu_i\chi,s)\Big)^{-1}\mathrm{localZeta30}(W,\chi,s,1),$$ with $L_v(\eta,s)=(1-\eta(\pi_v)(\mathrm{N}v)^{-s})^{-1}$ when $\eta$ has conductor exponent $0$ and $1$ otherwise, and $\varepsilon_v(\eta)$ the standard local root number at $1/2$.
--
--   This is the local functional equation, at a finite place of $\mathbb{Q}$ and on the strip $0<\operatorname{re}s<1$ where both integrals converge, relating the torus zeta integral of the long-Weyl translate of a $\mathrm{GL}_3$ Jacquet–Whittaker function to its dual; the gamma factor is the product over the three inducing characters of the $\mathrm{GL}_1$ local factors of Tate's theory. It is used in the construction of the Laurent expansion and functional equation of the local zeta integrals attached to `jacquetWhittaker3` translated by the antidiagonal matrix.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

theorem LanglandsTunnell.CubicInduction.localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (a : Fin 3 → ℕ) (ha : ∀ i, HasConductorExponentAt ℚ v (ν i * χ) (a i))
    (σ₀ σ₁ : ℝ)
    (h₀ : IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ 1 σ₀)
    (h₁ : IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (selfDualHaarAt ℚ v) (dualWhittakerFn3 (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)))
      χ⁻¹ (weylPrime3 * transposeInv3 1) σ₁)
    (s : ℂ) (hs₀ : σ₀ < s.re) (hs₁ : σ₁ < (1 - s).re) (hs : 0 < s.re) (hs' : s.re < 1) :
    localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ (1 - s) 1 =
      (∏ i, localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) *
        ((∏ i, stdRootNumberAt ℚ v (ν i * χ)) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s))) *
        ((∏ i, localLFactorAt ℚ v (ν i * χ) s)⁻¹ *
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
            (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ s 1) := by sorry
