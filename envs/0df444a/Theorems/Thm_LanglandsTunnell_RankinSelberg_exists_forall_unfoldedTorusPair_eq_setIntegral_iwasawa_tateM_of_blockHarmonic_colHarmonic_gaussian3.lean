-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_blockHarmonic_colHarmonic_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_blockHarmonic_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/6fc3e1fe-77ae-5afa-b0fe-aa13e19c732b
-- title:
--   Unfolded torus pair in Iwasawa coordinates, block-harmonic Gaussian section
-- statement:
--   The setting is the archimedean Rankin–Selberg frame attached to a cubic field and a twisting idele class character.
--
--   *Global data.* $K$ is a number field with $[K:\mathbb{Q}]=3$ (`_hdeg`), equipped with an integral algebra structure of $\mathcal{O}_\mathbb{Q}$ on $\mathcal{O}_K$, and $\mu\colon(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ is a character which is *admissible* (`_hμ`): trivial on the principal ideles $K^\times$, continuous, and of absolute value $1$ at every idele. The hypothesis `_hns` excludes descent of $\mu$ to $\mathbb{Q}$: there is no admissible character $\eta$ of $(\mathbb{A}_\mathbb{Q})^\times$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose trace $p=\mathfrak{P}\cap\mathcal{O}_\mathbb{Q}$ carries an unramified $\eta$, one has $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_{p})^{f(\mathfrak{P}/p)}$, where $\varpi$ denotes the uniformizer idele and $f$ the inertia degree. The families $uR,aR$ (indexed by the real places of $K$, with values in $\mathbb{C}$ and $\mathbb{Z}/2$) and $uC,kC$ (indexed by the complex places, with values in $\mathbb{C}$ and $\mathbb{Z}$) record the archimedean components of $\mu$: `huR` and `huC` state that for each place $w$ and each unit $x$ of the completion $K_w$, the local archimedean character of $\mu$ at $w$ equals $\|x\|^{\,\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$ with $(u,a)=(uR_w,(aR_w)\bmod 2$ lifted to $\mathbb{Z})$ at real places and $(u,a)=(uC_w,kC_w)$ at complex places.
--
--   *The descended character.* $\omega\colon(\mathbb{A}_\mathbb{Q})^\times\to\mathbb{C}^\times$ satisfies the three clauses of `hω`: $\omega$ is admissible in the above sense; for every prime $p$ of $\mathcal{O}_\mathbb{Q}$ which is not a bad place of $(K,\mu)$ — that is, $p$ is unramified in $K$ (every prime above it has ramification index $1$) and $\mu$ is unramified at every prime above it — $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals $\mathrm{inducedE3}$ at $p$ of the coefficient system $\mathfrak{P}\mapsto\mu(\varpi_{\mathfrak{P}})$ (zero at ramified $\mathfrak{P}$), namely minus the degree-$3$ coefficient of the induced Euler polynomial at $p$; and, for every choice of families $uR,aR,uC,kC$ satisfying the same archimedean compatibility conditions for $\mu$ and every real place $v$ of $\mathbb{Q}$, the archimedean component of $\omega$ at $v$ is given by the exponent $\sum_{w\text{ real}}uR_w+\sum_{w\text{ complex}}2\,uC_w$ and the integer $\sum_{w\text{ real}}(aR_w)^{\mathrm{val}}+\sum_{w\text{ complex}}(kC_w+1)$ (finite sums over the places of $K$).
--
--   *Adelic and measure-theoretic bookkeeping.* $E\colon(\mathbb{A}_{\mathbb{Q},\infty})^\times\to(\mathbb{A}_\mathbb{Q})^\times$ is a monoid homomorphism splitting the archimedean ideles, in the sense that the infinite part of $E(u)$ is $u$ and its finite part is $1$ (`hE`). The rational number $a$ is non-zero and equal to $-1$ (`ha`, `ha1`), $aInf$ is an archimedean idele unit whose underlying element is the image of $a$ (`haInf`), and $\psi_\infty$ is the additive character of $\mathbb{A}_{\mathbb{Q},\infty}$ given by $x\mapsto\psi_{\mathrm{arch}}(a\,x)$ (`hpsiInf`). The measure $\nu_{\mathrm{add}}$ on $\mathbb{A}_{\mathbb{Q},\infty}$ is $|a|^{1/2}$ times the transport of Lebesgue measure along the inverse of the identification of $\mathbb{A}_{\mathbb{Q},\infty}$ with the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the unit group. Measurable and Borel structures on $\mathbb{A}_{\mathbb{Q},\infty}$ and its units are assumed.
--
--   *The $GL_2(\mathbb{R})$ parameter and its Whittaker data.* $P$ is a real archimedean parameter, i.e. either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$ with $k\ge 1$; `_hP₁` requires $|\mathrm{Re}(u_1-u_2)|<1$ in the principal case. The data $kw$ (weights, indexed by a parity in $\mathbb{Z}/2$ and an infinite place of $\mathbb{Q}$), $Wr$ (torus functions $\mathbb{R}\to\mathbb{C}$) and $WA$ (functions on $GL_2(\mathbb{R})$) satisfy: `hkw1`, in the principal case $kw_{\mathrm{par}}=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$; `hkw2`, in the discrete case $kw_{\mathrm{par}}=k+1$; `hWr1`, in the principal case with equal parities $a_1=a_2$ and $\mathrm{par}=a_1$, the evenness/oddness relation $Wr(-t)=(-1)^{a_1}Wr(t)$; `hWr2`, in the discrete case $Wr_{\mathrm{par}}(t)=0$ for $t<0$; `hWr3`, in the principal case with $a_1=a_2$ and $\mathrm{par}=a_1+1$, the existence of $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin integral of $t\mapsto (Wr_{\mathrm{par}}(t)+(-1)^{a_1}Wr_{\mathrm{par}}(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$ at $s$; `hWr4`, for each parity and each $b$ equal to $\mathrm{par}$ or to $\mathrm{par}+P.\mathrm{centralSign}$, the same Mellin integral (with $(-1)^{b}$ in place of $(-1)^{a_1}$) converges for $\mathrm{Re}\,s$ large and equals the archimedean factor of $P$ twisted by $(0,b)$ at $s$, where the archimedean factor is the product of $\Gamma_\mathbb{R}$- and $\Gamma_\mathbb{C}$-factors attached to the parameter. The function $WA$ transforms under the unipotent subgroup by $WA(n(x)h)=e^{-2\pi i a x}WA(h)$ (`hWAN`), under scalars by $WA(z\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}}WA(h)$ (`hWAZ`), under the subgroup `rowIsometrySubgroup₀ ℝ` on the right by the weight character `archWeightCharℝ` of weight $kw_{\mathrm{par}}$ at the distinguished infinite place (`hWAK`), restricts on the torus to $WA_{\mathrm{par}}(\mathrm{diag}(t,1))=Wr_{\mathrm{par}}(t)$ (`hWAt`), and is continuous (`hWAc`). Finally $w_{0R}\in GL_2(\mathbb{R})$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   *The distinguished real place and the second parameter.* $w_0$ is a real place of $K$, and $P_2$ is a real archimedean parameter constrained by `hP₂` to one of two configurations: either $K$ has exactly three real places $w_0,w_1,w_2$ (pairwise distinct, exhausting the infinite places) and $P_2=\mathrm{principal}(uR_{w_1},aR_{w_1},uR_{w_2},aR_{w_2})$; or $K$ has exactly the places $w_0$ and one complex place $w_C$, and $P_2=\mathrm{discrete}(uC_{w_C},|kC_{w_C}|)$ if $kC_{w_C}\neq0$, while $P_2=\mathrm{principal}(uC_{w_C},0,uC_{w_C},1)$ if $kC_{w_C}=0$. Attached to $P_2$ is an archimedean datum $D$ of type `ArchDatumR P₂`: a function $D.W$ on real $2\times2$ matrices, smooth on the invertible locus, with $D.W(n(x)g)=\psi(x)D.W(g)$, the central law $D.W(z\cdot g)=\mathrm{centralChar}_{P_2}(z)\,|z|\,D.W(g)$, an entire completion of its zeta integrals $\int D.W(\mathrm{diag}(y,1)g)\,\chi_{u,a}(y)|y|^{s-1}\,d^\times y$ equal to the archimedean factor of $P_2$ twisted by $(u,a)$ times that entire function, with the functional equation relating $g$ and $wg$ through the epsilon factor, finite order in vertical strips, and prescribed decay of all derivatives towards $|y|\to\infty$ and $y\to0$. Together with an integer $k_0$, it satisfies: `hDW`, $D.W(x r)=\mathrm{archWeightChar}_\mathbb{R}(k_0)(r)\,D.W(x)$ for $r$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, the Casimir eigenvalue equation $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ at every $x$ with $\det x\neq0$; `hDnz`, $D.W$ is not identically zero; and `hk₀min`, the minimality of the weight: in the principal case $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, and in the discrete case $k_0=m+1$ where $m$ is the discrete parameter of $P_2$.
--
--   *The section.* A parity $\mathrm{par}_0\in\mathbb{Z}/2$, natural numbers $m,n,\delta$ with $\delta\in\{0,1\}$ (`hδ`), a sign $\varepsilon'=\pm1$ (`hε'`), and the Schwartz function $S$ on real $2\times3$ matrices given (`hS`) by
--   $$S(M)=(M_{00}M_{11}-M_{01}M_{10})^{\delta}\bigl((M_{00}+iM_{10})-i(M_{01}+iM_{11})\bigr)^{m}\bigl(M_{02}+\varepsilon' i M_{12}\bigr)^{n}e^{-\pi\sum_{i,b}M_{ib}^{2}}.$$
--
--   *Conclusion.* There exists $\sigma_1\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\mathrm{Re}\,s>\sigma_1$ the following equality of integrals holds. On the left, integration is over all $e\in\mathbb{R}^{2\times2}$ with respect to Lebesgue measure, of
--   $$\chi_{uR_{w_0}+2,\,aR_{w_0}}(\det e)\cdot\bigl(|\det e|^{2}\bigr)^{-1}\cdot\Bigl(\int_{\mathbb{R}}Wr_{\mathrm{par}_0}(t)\,D.W\bigl(\mathrm{diag}(at,1)\,e^{-1}\bigr)|t|^{\,s-1/2}\,(t^{2})^{-1}\,dt\Bigr)\cdot\Bigl(\int_{y>0}y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,\mathrm{godementInner3}\bigl(\psi_\infty\ast y,\,S,\,e,\,1\bigr)\,dy\Bigr),$$
--   where $\chi_{u,a}(y)=|y|^{u}$ times $1$ if $a=0$ and $\mathrm{sign}(y)$ otherwise, $Wr_{\mathrm{par}_0}$ is taken at the distinguished infinite place of $\mathbb{Q}$, $\psi_\infty\ast y$ denotes the multiplicative shift of $\psi_\infty$ by the archimedean element with all components $y$, and $\mathrm{godementInner3}(\psi,S,h,1)=\int_{v\in\mathbb{R}^2}S\bigl(h\cdot[\,\mathbf{e}_0+v_0\mathbf{e}_2;\ \mathbf{e}_1+v_1\mathbf{e}_2\,]\bigr)\psi(-v_1)\,dv$.
--
--   On the right, integration is over the set $\mathbb{R}\times\mathbb{R}\times(0,\infty)\times(0,2\pi]$ of quadruples $(x,y_1,y_2,\theta)$, with
--   $$g=\begin{pmatrix}y_1\cos\theta+xy_2\sin\theta & -y_1\sin\theta+xy_2\cos\theta\\ y_2\sin\theta & y_2\cos\theta\end{pmatrix},$$
--   of the product of: $\chi_{uR_{w_0}+2,\,aR_{w_0}}\bigl((y_1y_2)^{-1}\bigr)$; the factor $\bigl(|(y_1y_2)^{-1}|^{2}\bigr)^{-1}$; the torus integral $\int_{\mathbb{R}}Wr_{\mathrm{par}_0}(t)\,D.W\bigl(\mathrm{diag}(at,1)\,g\bigr)|t|^{\,s-1/2}(t^{2})^{-1}dt$; the explicit Tate–Mellin factor
--   $$\bigl((y_1y_2)^{-1}\bigr)^{\delta}\Bigl((\cos\theta-i\sin\theta)\bigl(\tfrac1{y_1}+\tfrac1{y_2}+i\tfrac{x}{y_1}\bigr)\Bigr)^{m}e^{-\pi\left(\frac{1+x^{2}}{y_1^{2}}+\frac1{y_2^{2}}\right)}|y_1y_2|\,(-ia)^{n}\bigl(y_2\sin\theta+\varepsilon' i\,y_2\cos\theta\bigr)^{n}\cdot\tfrac12\bigl(\pi a^{2}((y_2\sin\theta)^{2}+(y_2\cos\theta)^{2})\bigr)^{-\frac{W+n+1}{2}}\Gamma\!\left(\tfrac{W+n+1}{2}\right),$$
--   where $W=P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s$; and the Jacobian factor $y_2^{2}\bigl(|y_1y_2|^{4}\bigr)^{-1}$.
--
--   Only the equality of the two integrals is asserted; no integrability statement is part of the conclusion. The two sides are related by the substitution $e=g^{-1}$ in Iwasawa coordinates, and the inner $y$-integral on the left has been evaluated in closed form on the right.
--
--   This is the archimedean unfolding step in the Rankin–Selberg analysis of the cubic induction: the integral over $2\times2$ real matrices attached to the pair (torus Whittaker function for $P$, archimedean datum for $P_2$) and to a block-harmonic times column-harmonic Gaussian Schwartz section on $2\times3$ matrices is rewritten in Iwasawa coordinates $(x,y_1,y_2,\theta)$, with the Godement $y$-integral replaced by its explicit Gamma-function value. It is obtained from the unconditional Iwasawa change of variables [`LanglandsTunnell.RankinSelberg.integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional`](thm.html#LanglandsTunnell.RankinSelberg.integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional) together with the Tate–Mellin evaluation [`LanglandsTunnell.CubicInduction.integral_cpow_mul_godementInner3_mulShift_eq_mul_Gamma_of_blockPoly_mul_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.CubicInduction.integral_cpow_mul_godementInner3_mulShift_eq_mul_Gamma_of_blockPoly_mul_colHarmonic_gaussian3), and is used by the weight-one profile statement [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_blockHarmonic_colHarmonic_gaussian3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_blockHarmonic_colHarmonic_gaussian3
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (ha : a ≠ 0) (ha1 : a = -1) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (P : RealArchParam)
    (_hP₁ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (kw : ZMod 2 → InfinitePlace ℚ → ℤ)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
    (hkw1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par) + signShift (a₂ + par))
    (hkw2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hWr1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par ∨ b = par + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (hWAN : ∀ par : ZMod 2, ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
        WA par (unipotentGL2 x * h) = Complex.exp (-(2 * Real.pi * Complex.I * (a : ℂ) * x)) * WA par h)
    (hWAZ : ∀ par : ZMod 2, ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
        WA par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
          = ((((|(z : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
              (((z : ℝ) : ℂ) / ((|(z : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) * WA par h)
    (hWAK : ∀ par : ZMod 2, ∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA par (h * κ) = (archWeightCharℝ (kw par default) ⟨κ, hκ⟩ : ℂ) * WA par h)
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (hWAc : ∀ par : ZMod 2, Continuous (WA par))
    (w₀R : GL (Fin 2) ℝ) (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0])
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : LanglandsTunnell.Converse.ArchCasimir.IsCasimirEigen D)
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0)
    (hk₀min : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₀ = 0 ∨ k₀ = 1) ∧ ((k₀ : ZMod 2) = a₁ + a₂)) ∧
      (∀ (u : ℂ) (m : ℕ) (hm : 1 ≤ m), P₂ = RealArchParam.discrete u m hm → k₀ = (m : ℤ) + 1))
    (par₀ : ZMod 2) (m n δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (ε' : ℝ) (hε' : ε' = 1 ∨ ε' = -1)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M) :
    ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
      (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
        = ∫ p : ℝ × ℝ × ℝ × ℝ in Set.univ ×ˢ (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi))),
            (let x : ℝ := p.1
             let y₁ : ℝ := p.2.1
             let y₂ : ℝ := p.2.2.1
             let θ : ℝ := p.2.2.2
             let g : Matrix (Fin 2) (Fin 2) ℝ :=
               !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
                  y₂ * Real.sin θ, y₂ * Real.cos θ]
             ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (y₁ * y₂)⁻¹ *
                 (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
               ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * g) *
                   (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                (((((y₁ * y₂)⁻¹ : ℝ) : ℂ)) ^ δ *
                  ((((Real.cos θ : ℝ) : ℂ) - Complex.I * ((Real.sin θ : ℝ) : ℂ)) *
                      ((((1 / y₁ + 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ)))) ^ m *
                  (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
                  ((|y₁ * y₂| : ℝ) : ℂ) *
                  (-Complex.I * (a : ℂ)) ^ n *
                  (((y₂ * Real.sin θ : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) ^ n *
                  ((1 / 2 : ℂ) *
                    ((Real.pi * (a : ℝ) ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2) : ℝ) : ℂ)
                        ^ (-((P.centralExponent + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                    Complex.Gamma ((P.centralExponent + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
               ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) := by sorry
