-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/a60cae7f-31e1-5b9e-b8e6-56c43a80b79b
-- title:
--   Unfolded dual torus pair for the conjugate-harmonic weight-one section
-- statement:
--   The ambient data. $K$ is a number field, equipped with an algebra structure $\mathcal{O}_{\mathbb{Q}}\to\mathcal{O}_K$ that is integral, and $\mathrm{finrank}_{\mathbb{Q}}K=3$ is assumed ($\_hdeg$). A monoid homomorphism $\mu:\mathbb{A}_K^\times\to\mathbb{C}^\times$ is given which is an admissible twist (`IsAdmissibleTwist`: trivial on the principal ideles coming from $K^\times$, continuous, and of absolute value $1$ at every idele), together with the non-descent hypothesis $\_hns$: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every $\mathfrak{P}\in\mathrm{Spec}^1(\mathcal{O}_K)$ at which $\mu$ is unramified and with $\eta$ unramified at $\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ one has $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_{\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}})^{f}$, $f$ the residue degree `inertiaDeg'` of $\mathfrak{P}$ over $\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$, the uniformizer ideles being `uniformizerIdele`.
--
--   Archimedean exponents of $\mu$. Functions $u_R,a_R$ on the real places and $u_C,k_C$ on the complex places of $K$ (with values in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$ respectively) are given, and $h_{uR},h_{uC}$ assert `IsArchCompAt K μ w (uR w) ((aR w).val)` at each real place and `IsArchCompAt K μ w (uC w) (kC w)` at each complex place; that is, the local component of $\mu$ at $w$ sends $x\in (K_w)^\times$ to $\|x\|^{m_w u}\,(\sigma_w(x)/\|x\|)^{a}$, with $m_w$ the multiplicity of $w$ and $\sigma_w$ the embedding of $K_w$.
--
--   The rational companion character. A monoid homomorphism $\omega:\mathbb{A}_{\mathbb{Q}}^\times\to\mathbb{C}^\times$ is given with $h\omega$ a conjunction of three clauses: $\omega$ is an admissible twist of $\mathbb{Q}$; at every $p\in\mathrm{Spec}^1(\mathcal{O}_{\mathbb{Q}})$ which is not a bad place for $(K,\mu)$ (i.e. neither `IsRamifiedIn K` nor `IsTwistRamifiedAbove K μ` holds at $p$), $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, minus the degree-$3$ coefficient of the induced Euler polynomial formed from the unramified values of $\mu$; and, for every choice of archimedean exponent data $(u_R,a_R,u_C,k_C)$ for $\mu$ as above and every real place $v$ of $\mathbb{Q}$, `IsArchCompAt ℚ ω v` holds with exponent $\sum_{w\ \mathrm{real}}u_R(w)+\sum_{w\ \mathrm{complex}}2u_C(w)$ and integer parameter $\sum_{w\ \mathrm{real}}(a_R(w)).\mathrm{val}+\sum_{w\ \mathrm{complex}}(k_C(w)+1)$, the sums being finsums over the places.
--
--   Adelic normalisations. A monoid homomorphism $E:(\mathbb{A}_{\mathbb{Q},\infty})^\times\to\mathbb{A}_{\mathbb{Q}}^\times$ is given which splits the infinite part: [`M4aHerbrand.infPart (E u) = u`](def/M4aHerbrand_SIdeleClassGroup.html#L25) and [`RatIdele.finPart (E u) = 1`](def/RatIdele_Normalizer.html#L120) for all $u$. A rational number $a$ is given with $a\neq 0$ and $a=-1$; $a_{\inf}$ is a unit of the infinite adele ring whose underlying element is the image of $a$; and $\psi_\infty$ is an additive character of $\mathbb{A}_{\mathbb{Q},\infty}$ with $\psi_\infty(x)=\psi_{\mathrm{arch}}(a\,x)$ for the standard archimedean character `psiArch`. Measurable and Borel structures on $\mathbb{A}_{\mathbb{Q},\infty}$ and on its unit group are fixed; $\nu_{\mathrm{add}}$ is the measure $\mathrm{ofReal}(|a|^{1/2})$ times the image of Lebesgue measure under the inverse of the mixed-space ring equivalence, and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb{A}_{\mathbb{Q},\infty})^\times$.
--
--   The $GL_2$ archimedean Whittaker data over $\mathbb{Q}$. A real archimedean parameter $P$ (a `RealArchParam`, either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$ with $k\geq 1$) is given, with $\_hP_1$: in the principal case $|\Re(u_1-u_2)|<1$. Further data are weights $kw:\mathbb{Z}/2\to\{\text{places of }\mathbb{Q}\}\to\mathbb{Z}$, radial profiles $W_r:\mathbb{Z}/2\to\{\text{places}\}\to\mathbb{C}\to\mathbb{C}$ and functions $W_A:\mathbb{Z}/2\to GL_2(\mathbb{R})\to\mathbb{C}$, subject to: $hkw1$, in the principal case $kw(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ at real $w$, where $\mathrm{signShift}(b)$ is $0$ for $b=0$ and $1$ otherwise; $hkw2$, in the discrete case of weight $n$, $kw(\mathrm{par},w)=n+1$; $hWr1$, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$ then $W_r(\mathrm{par},w,-t)=(-1)^{a_1.\mathrm{val}}W_r(\mathrm{par},w,t)$; $hWr2$, in the discrete case $W_r(\mathrm{par},w,t)=0$ for $t<0$; $hWr3$, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$ then for some $s_0$ and all $s$ with $\Re s>s_0$ the Mellin integral of $t\mapsto (W_r(\mathrm{par},w,t)+(-1)^{a_1.\mathrm{val}}W_r(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}\,\mathrm{archFactor}(P.\mathrm{twist}\,0\,a_1)(s)$; $hWr4$, for every $\mathrm{par}$ and every $b$ with $b=\mathrm{par}$ or $b=\mathrm{par}+P.\mathrm{centralSign}$, the same Mellin transform with $(-1)^{b.\mathrm{val}}$ converges for $\Re s$ large and equals $\mathrm{archFactor}(P.\mathrm{twist}\,0\,b)(s)$; $hWAN$, $W_A(\mathrm{par})(u(x)h)=e^{-2\pi i a x}W_A(\mathrm{par})(h)$ for the unipotent $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; $hWAZ$, $W_A(\mathrm{par})(z\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}W_A(\mathrm{par})(h)$ for scalar $z\in\mathbb{R}^\times$; $hWAK$, $W_A(\mathrm{par})(h\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(kw(\mathrm{par},\mathrm{default}))(\kappa)\,W_A(\mathrm{par})(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; $hWAt$, $W_A(\mathrm{par})(\mathrm{diag}(t,1))=W_r(\mathrm{par},\mathrm{default},t)$; and $hWAc$, continuity of each $W_A(\mathrm{par})$. An element $w_{0R}\in GL_2(\mathbb{R})$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ is fixed.
--
--   The distinguished place and the Levi datum. A real place $w_0$ of $K$ is fixed. A second real parameter $P_2$ is given together with $hP_2$, the disjunction: either $K$ has exactly the three pairwise distinct real places $w_0,w_1,w_2$ and $P_2=\mathrm{principal}(u_R(w_1),a_R(w_1),u_R(w_2),a_R(w_2))$; or $K$ has a complex place $w_C$ and its places are exactly $w_C$ and $w_0$, and either $k_C(w_C)\neq 0$ and $P_2=\mathrm{discrete}(u_C(w_C),|k_C(w_C)|)$, or $k_C(w_C)=0$ and $P_2=\mathrm{principal}(u_C(w_C),0,u_C(w_C),1)$. An `ArchDatumR P_2` datum $D$ (a Whittaker function $D.W$ on $2\times 2$ real matrices, smooth on the invertible locus, with unipotent and central transformation laws, entire twisted zeta integrals satisfying the functional equation for $P_2$, of finite order and with the prescribed decay) and an integer $k_0$ are given, with: $hDW$, $D.W(x\,r)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(r)\,D.W(x)$ for $r$ in `rowIsometrySubgroup₀ ℝ`; $hDE$, $D$ is a Casimir eigenfunction, i.e. $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x\neq 0$; $hDnz$, $D.W$ is not identically zero; $hk_{0\min}$, in the principal case $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, and in the discrete case of weight $m$, $k_0=m+1$.
--
--   Weight-one and section data. $hPw1$ asserts $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $a_1\neq a_2$; $hk_0$ asserts $1\leq k_0$; $n$ is a natural number with $n=k_0-1$; $\mathrm{par}_0\in\mathbb{Z}/2$ is arbitrary. The section $S$ on $2\times 3$ real matrices is, writing $\bar z_j(M)=M_{0j}-iM_{1j}$,
--   $$S(M)=\bigl(\bar z_0(M)-i\,\bar z_1(M)\bigr)\,\bar z_2(M)^{\,n}\,\exp\Bigl(-\pi\sum_{i,b}M_{ib}^2\Bigr),$$
--   the last factor being `gaussian3 M`. Finally $s\in\mathbb{C}$ is arbitrary.
--
--   Conclusion. For the given $s$ the following equality of iterated Lebesgue integrals holds, the outer variable $a_2$ ranging over $(0,\infty)$ and the inner variable $a_1$ over $\mathbb{R}$, both integrands being defined to vanish unless $a_1\neq 0$ and $0<a_2$. On the left, with $q=\mathrm{upperUnit}(a_1,0,a_2)=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}\in GL_2(\mathbb{R})$, the integrand is
--   $$\bigl|\det q\bigr|\;W_A(\mathrm{par}_0)\bigl(w_{0R}\cdot{}^{t}q^{-1}\bigr)\cdot \mathcal{J}^{\vee}\bigl(\mathrm{arch}_3(\iota(q_\infty))\bigr)\cdot\bigl|\det q\bigr|^{\,s-\frac12}\cdot a_1^{-2},$$
--   where ${}^tq^{-1}$ is [`RSCarrier.transposeInv q`](def/LanglandsTunnell_RSCarrier.html#L31); $q_\infty$ denotes the image of $q$ under `archRealGLAt` at the real place $\mathrm{default}$ of $\mathbb{Q}$ into $GL_2(\mathbb{A}_{\mathbb{Q}})$, pushed by `iota` into $GL_3(\mathbb{A}_{\mathbb{Q}})$ and then to its archimedean component by `archComponent3`; and $\mathcal{J}^{\vee}=\mathrm{dualWhittakerFn3}$ applied to the Jacquet vector $\mathrm{jacquetVector3}\,D\,(u_R(w_0))\,(a_R(w_0))\,a\,\psi_\infty\,S$, i.e. the value of that vector at $\mathrm{longWeyl}_3\cdot{}^{t}(\cdot)^{-1}$ of its argument.
--
--   On the right the integrand is the product of four factors:
--   $$\bigl|a_1a_2\bigr|\cdot\Bigl(i^{\,kw(\mathrm{par}_0,\mathrm{default})}\cdot\bigl|-a_1^{-1}\bigr|^{\,P.\mathrm{centralExponent}+1}\Bigl(\tfrac{-a_1^{-1}}{|-a_1^{-1}|}\Bigr)^{P.\mathrm{centralSign}.\mathrm{val}}\cdot W_r\bigl(\mathrm{par}_0,\mathrm{default},-a_1/a_2\bigr)\Bigr),$$
--   then
--   $$\chi_{u_R(w_0)+1,\,a_R(w_0)}\bigl(-(a_1a_2)^{-1}\bigr)\cdot\int_{e\in M_2(\mathbb{R})}G(e)\cdot\chi_{u_R(w_0)+2,\,a_R(w_0)}(\det e)\,|\det e|^{-2}\cdot D.W\bigl(\mathrm{diag}(a,1)\,e^{-1}\bigr)\,de,$$
--   then $|a_1a_2|^{\,s-\frac12}$, then $a_1^{-2}$. Here $\chi_{u,b}(y)=|y|^{u}$ if $b=0$ and $|y|^{u}\,\mathrm{sign}(y)$ otherwise (`ArchR.quasiChar`), $\mathrm{diag}(a,1)$ is `ArchR.diagOne a`, and the inner kernel is
--   $$G(e)=(e_{00}-ie_{10})^{n}\,e^{-\pi\left(a_2^{-2}(e_{01}^2+e_{11}^2)+(e_{00}^2+e_{10}^2)\right)}\cdot\frac{a_1^{2}}{|\det e|}\cdot\bigl(-i\bigl(a\,a_1\,(\rho_0-i\rho_1)+a_2^{-1}(e_{01}-ie_{11})\bigr)\bigr)\cdot e^{-\pi a^{2}a_1^{2}(\rho_0^2+\rho_1^2)},$$
--   with $\rho_0=(e^{-1})_{10}$ and $\rho_1=(e^{-1})_{11}$.
--
--   The global data $\mu$, $\omega$, $E$, $a_{\inf}$ and the measures $\nu_{\mathrm{add}},\nu_{\mathrm{mul}}$ are part of the frame in which the identity is recorded; the two sides of the conclusion involve only $a$, $\psi_\infty$, $kw$, $W_r$, $W_A$, $P$, $w_{0R}$, $D$, $u_R(w_0)$, $a_R(w_0)$, $n$, $\mathrm{par}_0$, $S$ and $s$.
--
--   This is the dual-side unfolding step of the archimedean Rankin–Selberg computation for the cubic induction: the $(a_1,a_2)$-integral of the dual torus pair built from the $GL_2$ Whittaker function $W_A$ and the $GL_3$ Jacquet vector of the conjugate-block-harmonic weight-one Gaussian section is rewritten as an explicit integral over the Siegel coordinates $a_1,a_2$ and the matrix variable $e$. It feeds the two statements which identify this pair with the archimedean root number times an explicit factor times the gamma factor, in the discrete and the weight-one profile cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3.lean

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

theorem LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3
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
    (hPw1 : ∃ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ ∧ a₁ ≠ a₂)
    (hk₀ : 1 ≤ k₀)
    (n : ℕ) (hn : (n : ℤ) = k₀ - 1)
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (s : ℂ) :
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
      = (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                ((((|a₁ * a₂| : ℝ) : ℂ) *
                    (Complex.I ^ (kw par₀ default) *
                      ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
                        ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) *
                      Wr par₀ default (-a₁ / a₂))) *
                  (ArchR.quasiChar (uR w₀ h₀ + 1) (aR w₀ h₀) (-(a₁ * a₂)⁻¹) *
                    ∫ e : Fin 2 → Fin 2 → ℝ,
                      ((((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ n *
                    (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
                    (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
                    (-Complex.I *
                      ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) - Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) +
                        (a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) - Complex.I * ((e 1 1 : ℝ) : ℂ)))) *
                    (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
                        (ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) *
                        D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹)) *
                  (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0) := by sorry
