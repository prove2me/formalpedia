-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_minorSection_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_minorSection_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/7b52cbd5-cefe-5942-b826-b21bd09cef32
-- title:
--   Iwasawa and Tate–Mellin form of the minor-section torus pair
-- statement:
--   The statement is set in the archimedean frame of the cubic-induction Rankin–Selberg argument, and its hypotheses fall into the following groups.
--
--   *Global data over a cubic field.* $K$ is a number field whose ring of integers carries an integral $\mathcal O_{\mathbb Q}$-algebra structure, with $\operatorname{finrank}_{\mathbb Q}K=3$ (the hypothesis `_hdeg`). A character $\mu\colon(\mathbb A_K)^{\times}\to\mathbb C^{\times}$ is given, and `_hμ` asserts `IsAdmissibleTwist K μ`, i.e. $\mu$ is trivial on the principal ideles $K^{\times}$, continuous, and unitary ($|\mu(x)|=1$ for all $x$). The hypothesis `_hns` excludes descent of $\mu$ to $\mathbb Q$: there is no admissible twist $\eta$ of $\mathbb Q$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and with $\eta$ unramified at the prime $p=\mathfrak P\cap\mathcal O_{\mathbb Q}$ below it one has $\mu(\varpi_{\mathfrak P})=\eta(\varpi_{p})^{f}$, where $\varpi$ denotes the idele which is a uniformiser at the given place and trivial elsewhere and $f=\operatorname{inertiaDeg'}$ of $\mathfrak P$ over $p$. Here unramifiedness of a character at a finite place $v$ means that its local component is trivial on the units of the valuation ring of the completion.
--
--   *Archimedean components of $\mu$.* Functions $u_R(w)\in\mathbb C$, $a_R(w)\in\mathbb Z/2$ are given at each real place $w$ of $K$, and $u_C(w)\in\mathbb C$, $k_C(w)\in\mathbb Z$ at each complex place. The hypotheses `huR`, `huC` assert `IsArchCompAt`, namely that the archimedean local component of $\mu$ at $w$ is $x\mapsto \|x\|^{\,\mathrm{mult}(w)\,u}\,(\iota_w(x)/\|x\|)^{a}$, with $(u,a)=(u_R(w),(a_R(w))_{\mathrm{val}})$ at real places and $(u,a)=(u_C(w),k_C(w))$ at complex places.
--
--   *The determinant character $\omega$.* A character $\omega\colon(\mathbb A_{\mathbb Q})^{\times}\to\mathbb C^{\times}$ is given, and `hω` is a conjunction of three clauses: $\omega$ is an admissible twist of $\mathbb Q$; for every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ — that is, no prime of $\mathcal O_K$ above $p$ has ramification index $\neq 1$ and $\mu$ is unramified at every prime above $p$ — the character $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, minus the degree-$3$ coefficient of the induced Euler polynomial built from the unramified Frobenius values of $\mu$ ($\mu(\varpi_{\mathfrak P})$ where $\mu$ is unramified at $\mathfrak P$, and $0$ otherwise); and, for any data $u_R,a_R,u_C,k_C$ satisfying the two `IsArchCompAt` conditions for $\mu$ (the quantifiers being repeated inside this clause), the component of $\omega$ at the real place $v$ of $\mathbb Q$ is given by `IsArchCompAt ℚ ω v` with exponent $\sum_{w\ \mathrm{real}}u_R(w)+\sum_{w\ \mathrm{complex}}2u_C(w)$ and integer $\sum_{w\ \mathrm{real}}(a_R(w))_{\mathrm{val}}+\sum_{w\ \mathrm{complex}}(k_C(w)+1)$, the sums being finite sums over the infinite places.
--
--   *Splitting of the ideles at infinity.* A monoid homomorphism $E\colon(\mathbb A_{\mathbb Q,\infty})^{\times}\to(\mathbb A_{\mathbb Q})^{\times}$ is given with `hE`: the infinite part of $E(u)$ is $u$ and the finite part of $E(u)$ is $1$.
--
--   *Additive character and measures.* A rational number $a$ is given with $a\neq 0$ and $a=-1$; $a_\infty$ is a unit of $\mathbb A_{\mathbb Q,\infty}$ whose underlying element is the image of $a$; $\psi_\infty$ is an additive character of $\mathbb A_{\mathbb Q,\infty}$ with $\psi_\infty(x)=\psi_{\mathrm{arch}}(a x)$ for the standard archimedean character $\psi_{\mathrm{arch}}$. Alongside the Borel measurable structures on $\mathbb A_{\mathbb Q,\infty}$ and its unit group, a measure $\nu_{\mathrm{add}}$ on $\mathbb A_{\mathbb Q,\infty}$ is given with $\nu_{\mathrm{add}}=|a|^{1/2}\cdot$ (the pushforward of Lebesgue measure on the mixed space under the inverse of the ring equivalence `InfiniteAdeleRing.ringEquiv_mixedSpace ℚ`), and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb A_{\mathbb Q,\infty})^{\times}$.
--
--   *The first archimedean parameter and its Whittaker data.* $P$ is a real archimedean parameter, either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb C$, $a_i\in\mathbb Z/2$ or $\mathrm{discrete}(u,k)$ with $k\geq 1$; `_hP₁` requires $|\operatorname{Re}(u_1-u_2)|<1$ in the principal case. Data $k_w\colon\mathbb Z/2\times\{\text{infinite places of }\mathbb Q\}\to\mathbb Z$, $W_r\colon\mathbb Z/2\times\{\text{places}\}\times\mathbb R\to\mathbb C$ and $W_A\colon\mathbb Z/2\times GL_2(\mathbb R)\to\mathbb C$ are given, subject to: `hkw1`, in the principal case $k_w(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$; `hkw2`, in the discrete case $k_w(\mathrm{par},w)=k+1$; `hWr1`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$ then $W_r(\mathrm{par},w,-t)=(-1)^{(a_1)_{\mathrm{val}}}W_r(\mathrm{par},w,t)$; `hWr2`, in the discrete case $W_r(\mathrm{par},w,t)=0$ for $t<0$; `hWr3`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$, then for some $\sigma_0$ and all $s$ with $\operatorname{Re}s>\sigma_0$ the Mellin transform of $t\mapsto(W_r(\mathrm{par},w,t)+(-1)^{(a_1)_{\mathrm{val}}}W_r(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}\cdot(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$; `hWr4`, for $b\in\mathbb Z/2$ equal to $\mathrm{par}$ or to $\mathrm{par}+P.\mathrm{centralSign}$, the same Mellin transform with $(-1)^{b_{\mathrm{val}}}$ converges in a right half-plane and equals $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$ — here $\mathrm{archFactor}$ is the product of $\Gamma_{\mathbb R}(s+u_i+\mathrm{signShift}(a_i))$ in the principal case and $\Gamma_{\mathbb C}(s+u+k/2)$ in the discrete case, $\mathrm{twist}\,0\,b$ shifts the signs by $b$, and $\mathrm{centralSign}$ is $a_1+a_2$, resp. $k+1$; `hWAN`, $W_A(\mathrm{par},n(x)h)=e^{-2\pi i a x}W_A(\mathrm{par},h)$ for unipotent $n(x)$; `hWAZ`, $W_A(\mathrm{par},zI\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{(P.\mathrm{centralSign})_{\mathrm{val}}}W_A(\mathrm{par},h)$ for $z\in\mathbb R^{\times}$, the central exponent being $u_1+u_2$, resp. $2u$; `hWAK`, $W_A(\mathrm{par},h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_w(\mathrm{par},\mathrm{default}))(\kappa)\,W_A(\mathrm{par},h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, $W_A(\mathrm{par},\mathrm{diag}(t,1))=W_r(\mathrm{par},\mathrm{default},t)$ for $t\in\mathbb R^{\times}$; and `hWAc`, continuity of $W_A(\mathrm{par},\cdot)$ for each parity.
--
--   *The second parameter, the Levi Whittaker datum, and the test function.* $w_{0R}\in GL_2(\mathbb R)$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$; $w_0$ is a real place of $K$. A second real archimedean parameter $P_2$ is given, and `hP₂` is the disjunction: either there are two further real places $w_1,w_2$ of $K$, distinct from each other and from $w_0$, such that every infinite place of $K$ is one of $w_0,w_1,w_2$, and $P_2=\mathrm{principal}(u_R(w_1),a_R(w_1),u_R(w_2),a_R(w_2))$; or there is a complex place $w_C$ such that every infinite place is $w_C$ or $w_0$, and either $k_C(w_C)\neq 0$ and $P_2=\mathrm{discrete}(u_C(w_C),|k_C(w_C)|)$, or $k_C(w_C)=0$ and $P_2=\mathrm{principal}(u_C(w_C),0,u_C(w_C),1)$. Further, $D$ is an `ArchDatumR P_2`, that is a function $W_D$ on $2\times 2$ real matrices which is smooth on the invertible locus, satisfies the unipotent law $W_D(n(x)g)=\psi(x)W_D(g)$ and the central law $W_D(zg)=\mathrm{centralChar}_{P_2}(z)|z|W_D(g)$, and is equipped with entire completed zeta functions whose Mellin integrals equal $(P_2.\mathrm{twist}\,u\,a).\mathrm{archFactor}(s)$ times them, with the functional equation given by the epsilon factor of $P_2.\mathrm{twist}\,u\,a$, finite order in vertical strips, and the prescribed decay at large and small $|y|$. An integer $k_0$ is given with `hDW`: $W_D(x\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(\kappa)W_D(x)$ for $\kappa\in$ `rowIsometrySubgroup₀ ℝ`; `hDE`: $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(W_D)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot W_D(x)$ for all $x$ with $\det x\neq0$, where $\mathrm{matrixCasimir}(W)=-\big(\tfrac14 H^2W-\tfrac12 HW+EF^{-}W\big)$ in the matrix flow derivatives and the eigenvalue is $\tfrac14-\big(\tfrac{u_1-u_2}{2}\big)^2$, resp. $\tfrac{1-k^2}{4}$; `hDnz`: $W_D$ does not vanish identically; and `hk₀min`: in the principal case $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, while in the discrete case $k_0=k+1$. Finally a parity $\mathrm{par}_0\in\mathbb Z/2$ is fixed, and $S$ is the minor-section Gaussian datum on $2\times 3$ real matrices,
--   $$S(M)=\big((M_{00}-iM_{01})M_{12}-(M_{10}-iM_{11})M_{02}\big)\,e^{-\pi\sum_{i,b}M_{ib}^2}.$$
--
--   *Conclusion.* There exists $\sigma_1\in\mathbb R$ such that for every $s\in\mathbb C$ with $\operatorname{Re}s>\sigma_1$ the following identity of complex numbers holds. Writing $\chi_{u,\alpha}(y)=|y|^{u}$ times $1$ if $\alpha=0$ and $\operatorname{sign}(y)$ otherwise, $\mathrm{diag}(y,1)=\begin{pmatrix}y&0\\0&1\end{pmatrix}$, $w=P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s$, and $I_S(y,e)=\mathrm{godementInner3}\big(\psi_\infty^{(y)},S,e,1\big)=\int_{v\in\mathbb R^2}S\big(e\cdot[\,\text{rows }m_{0b}+v_0m_{2b},\ m_{1b}+v_1m_{2b}\,]\big)\,\psi_\infty^{(y)}(\iota(-v_1))\,dv$ for $m=1$, where $\psi_\infty^{(y)}$ is $\psi_\infty$ shifted by the infinite adele $\iota(y)$ with value $y$ at each place, the left-hand side is the integral over all $2\times2$ real matrices $e$ (Lebesgue measure on $\mathbb R^4$)
--   $$\int_{e}\chi_{u_R(w_0)+2,\,a_R(w_0)}(\det e)\,\big(|\det e|^{2}\big)^{-1}\Big(\int_{\mathbb R}W_r(\mathrm{par}_0,\mathrm{default},t)\,W_D\big(\mathrm{diag}(at,1)\,e^{-1}\big)\,|t|^{\,s-1/2}\,(t^{2})^{-1}\,dt\Big)\Big(\int_{0}^{\infty}y^{\,w}\,I_S(y,e)\,dy\Big),$$
--   and the right-hand side is the integral over the set $\mathbb R\times\mathbb R\times(0,\infty)\times(0,2\pi]$ of quadruples $p=(x,y_1,y_2,\theta)$, with
--   $$g=\begin{pmatrix}y_1\cos\theta+xy_2\sin\theta&-y_1\sin\theta+xy_2\cos\theta\\ y_2\sin\theta&y_2\cos\theta\end{pmatrix},$$
--   of
--   $$\chi_{u_R(w_0)+2,\,a_R(w_0)}\big((y_1y_2)^{-1}\big)\big(|(y_1y_2)^{-1}|^{2}\big)^{-1}\Big(\int_{\mathbb R}W_r(\mathrm{par}_0,\mathrm{default},t)\,W_D\big(\mathrm{diag}(at,1)\,g\big)|t|^{\,s-1/2}(t^{2})^{-1}dt\Big)\cdot$$
--   $$\cdot\Big(e^{-\pi\left(\frac{1+x^{2}}{y_1^{2}}+\frac{1}{y_2^{2}}\right)}\,|y_1y_2|\,(-ia)\,\frac{y_2}{y_1}\,(1+ix)\cdot\tfrac12\big(\pi a^{2}\big((y_2\sin\theta)^{2}+(y_2\cos\theta)^{2}\big)\big)^{-\frac{w+2}{2}}\Gamma\!\Big(\frac{w+2}{2}\Big)\Big)\cdot\frac{y_2^{2}}{|y_1y_2|^{4}}.$$
--   Thus the inner $y$-integral has been replaced by its closed Godement–Tate form and the matrix integral by its Iwasawa-coordinate form, the last factor being the associated Jacobian density.
--
--   The conclusion involves only $u_R(w_0)$, $a_R(w_0)$, $a$, $\psi_\infty$, $S$, $P$, $P_2$, $W_r(\mathrm{par}_0,\cdot)$ and $W_D$; the remaining data above are the ambient hypotheses of the surrounding archimedean pairing argument.
--
--   This is the archimedean unfolding step of the Rankin–Selberg pairing in the cubic-induction (Langlands–Tunnell converse) argument for the minor-section Gaussian test function: the zeta integral over $GL_2(\mathbb R)$ is written in Iwasawa coordinates $(x,y_1,y_2,\theta)$ and the Godement–Tate inner integral in the extra variable is evaluated as a power of $\pi a^2(\,\cdot\,)$ times a Gamma value. It is cited by [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile), where the resulting explicit integral is identified with a product of Gamma factors in the weight-one case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_minorSection_gaussian3.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_minorSection_gaussian3
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
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 0 1 : ℝ) : ℂ)) * ((M 1 2 : ℝ) : ℂ) -
        (((M 1 0 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ)) * ((M 0 2 : ℝ) : ℂ)) * gaussian3 M) :
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
                ((Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
                  ((|y₁ * y₂| : ℝ) : ℂ) *
                  (-Complex.I * (a : ℂ)) *
                  (((y₂ / y₁ : ℝ) : ℂ) * (1 + Complex.I * (x : ℂ))) *
                  ((1 / 2 : ℂ) *
                    ((Real.pi * (a : ℝ) ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2) : ℝ) : ℂ)
                        ^ (-((P.centralExponent + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
                    Complex.Gamma ((P.centralExponent + P₂.centralExponent + 2 * s + 1 + 1) / 2)))) *
               ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) := by sorry
