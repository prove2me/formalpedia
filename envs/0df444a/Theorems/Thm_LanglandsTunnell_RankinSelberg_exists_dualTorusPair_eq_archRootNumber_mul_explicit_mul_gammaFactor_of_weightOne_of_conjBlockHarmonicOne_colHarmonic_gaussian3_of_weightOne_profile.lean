-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_weightOne_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_weightOne_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/04a049a6-51c5-52b9-96c5-ad59ff12e5a4
-- title:
--   Folded dual torus pair: root number, explicit constant, dual Γ-factors
-- statement:
--   The setting is a number field $K$ of degree $3$ over $\mathbb Q$ (the hypothesis `_hdeg` asserts $\operatorname{finrank}_{\mathbb Q}K=3$), together with an integral algebra structure of $\mathcal O_K$ over $\mathcal O_{\mathbb Q}$, and a character $\mu\colon(\mathbb A_K)^\times\to\mathbb C^\times$ which is an admissible twist, i.e. trivial on the principal ideles $K^\times$, continuous, and of absolute value $1$ everywhere (`_hμ`). The hypothesis `_hns` excludes base change from $\mathbb Q$: there is no admissible twist $\eta$ of $\mathbb Q$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and at whose restriction $p=\mathfrak P\cap\mathcal O_{\mathbb Q}$ the character $\eta$ is unramified, the value $\mu(\varpi_{\mathfrak P})$ equals $\eta(\varpi_{p})$ raised to the inertia degree of $\mathfrak P$ over $p$; here $\varpi$ denotes the idele `uniformizerIdele` concentrated at the given place, and unramifiedness means that the local component is trivial on the units of the local integers.
--
--   The archimedean profile of $\mu$ is recorded by functions $uR(w)\in\mathbb C$, $aR(w)\in\mathbb Z/2$ for the real places $w$ of $K$ and $uC(w)\in\mathbb C$, $kC(w)\in\mathbb Z$ for the complex ones, the hypotheses `huR`, `huC` asserting `IsArchCompAt`: the local archimedean component of $\mu$ at $w$ sends $x$ to $\|x\|^{\operatorname{mult}(w)\,u}\,(\iota_w(x)/\|x\|)^{a}$ with $(u,a)=(uR(w),(aR(w)).\mathrm{val})$ at real places and $(u,a)=(uC(w),kC(w))$ at complex places.
--
--   Further, $\omega$ is a character of $(\mathbb A_{\mathbb Q})^\times$ subject to the three-clause hypothesis `hω`: $\omega$ is an admissible twist of $\mathbb Q$; at every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ (that is, $p$ is unramified in $K$ and the twist is unramified above $p$), $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals $\operatorname{inducedE3}$ of the coefficient system $\mathfrak P\mapsto\mu(\varpi_{\mathfrak P})$ (defined as minus the degree-$3$ coefficient of the induced Euler polynomial at $p$); and, for every quadruple $(uR,aR,uC,kC)$ describing the archimedean components of $\mu$ as above, at each real place $v$ of $\mathbb Q$ the character $\omega$ has archimedean component with exponent $\sum_{w\ \mathrm{real}}uR(w)+\sum_{w\ \mathrm{complex}}2\,uC(w)$ and integer $\sum_{w\ \mathrm{real}}(aR(w)).\mathrm{val}+\sum_{w\ \mathrm{complex}}(kC(w)+1)$.
--
--   The remaining global data are: a monoid homomorphism $E$ from the units of the infinite adele ring of $\mathbb Q$ to the ideles, splitting the infinite part and with trivial finite part (`hE`); a rational number $a$ with $a\neq0$ and $a=-1$, a unit $a_{\infty}$ of the infinite adele ring whose underlying element is the image of $a$; the additive character $\psi_\infty$ with $\psi_\infty(x)=\psi_{\mathrm{arch}}(a\,x)$ for the standard archimedean character $\psi_{\mathrm{arch}}$ of $\mathbb Q$; measurable and Borel structures on the infinite adele ring and its unit group; the additive measure $\nu_{\mathrm{add}}=|a|^{1/2}\cdot$ (pushforward of Lebesgue measure along the inverse of the identification of the infinite adele ring with the mixed space) and a Haar measure $\nu_{\mathrm{mul}}$ on the unit group.
--
--   The archimedean parameter of the $\mathrm{GL}_2$ input is $P\colon$ `RealArchParam`, with the hypothesis `_hP₁` that whenever $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ one has $|\operatorname{Re}(u_1-u_2)|<1$. Attached to $P$ are a weight function $kw\colon\mathbb Z/2\times\{\text{infinite places of }\mathbb Q\}\to\mathbb Z$, torus functions $Wr(\mathrm{par},w)\colon\mathbb C\to\mathbb C$ and Whittaker functions $WA(\mathrm{par})\colon\mathrm{GL}_2(\mathbb R)\to\mathbb C$, subject to the following groups of hypotheses. Weight (`hkw1`, `hkw2`): in the principal case $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ one has $kw(\mathrm{par},w)=\operatorname{signShift}(a_1+\mathrm{par})+\operatorname{signShift}(a_2+\mathrm{par})$, where $\operatorname{signShift}(0)=0$ and $\operatorname{signShift}(1)=1$; in the discrete case $P=\mathrm{discrete}(u_0,n)$ with $n\ge1$ one has $kw(\mathrm{par},w)=n+1$. Torus profile (`hWr1`–`hWr4`): if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$ then $Wr(\mathrm{par},w)(-t)=(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(t)$ for real $t$; if $P$ is discrete then $Wr(\mathrm{par},w)$ vanishes on the negative reals; if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$ then there is $s_0$ such that for $\operatorname{Re}s>s_0$ the Mellin transform of $t\mapsto (Wr(\mathrm{par},w)(t)+(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}\,(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$; and for every $\mathrm{par}$ and every $b$ with $b=\mathrm{par}$ or $b=\mathrm{par}+P.\mathrm{centralSign}$ there is $s_0$ such that for $\operatorname{Re}s>s_0$ the Mellin transform of the corresponding folded function $t\mapsto (Wr(\mathrm{par},w)(t)+(-1)^{b.\mathrm{val}}Wr(\mathrm{par},w)(-t))/t$ converges and equals $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$, where the arch factor of a real parameter is the product of $\Gamma_{\mathbb R}(s+\cdot)$ over its $\Gamma_{\mathbb R}$-multiset times the product of $\Gamma_{\mathbb C}(s+\cdot)$ over its $\Gamma_{\mathbb C}$-multiset. Whittaker laws (`hWAN`, `hWAZ`, `hWAK`, `hWAt`, `hWAc`): $WA(\mathrm{par})$ transforms under the upper unipotent $\binom{1\ x}{0\ 1}$ by $\exp(-2\pi i a x)$, under the scalar matrix $z$ by $|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}$, under right translation by $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ` by the character $\operatorname{archWeightChar}_{\mathbb R}(kw(\mathrm{par},\text{default place}))$, restricts on the torus $\operatorname{diag}(t,1)$ to $Wr(\mathrm{par},\text{default place})(t)$, and is continuous.
--
--   On the side of $K$: $w_0^R$ is the element of $\mathrm{GL}_2(\mathbb R)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $w_0$ is a real place of $K$, and $P_2$ is a real archimedean parameter constrained by `hP₂` to one of two shapes: either $K$ has exactly three real places $w_0,w_1,w_2$ (pairwise distinct, exhausting the infinite places) and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$; or the infinite places of $K$ are $w_0$ and a single complex place $w_C$, and then $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$ if $kC(w_C)\neq0$, while $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$ if $kC(w_C)=0$.
--
--   Attached to $P_2$ are an archimedean datum $D\colon$ `ArchDatumR P₂` (a Whittaker function $D.W$ on $2\times2$ real matrices, smooth on the invertible locus, with the unipotent and central transformation laws and the zeta-integral package, functional equation and growth and decay bounds carried by that structure) and an integer $k_0$, with: `hDW`, right equivariance $D.W(x\kappa)=\operatorname{archWeightChar}_{\mathbb R}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, the Casimir eigenvalue equation $\operatorname{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ at all $x$ with $\det x\neq0$; `hDnz`, non-vanishing of $D.W$ at some point; `hk₀min`, which requires $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$ when $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$, and $k_0=m+1$ when $P_2=\mathrm{discrete}(u,m)$. Moreover `hPw1` requires $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $a_1\neq a_2$, `hk₀` requires $1\le k_0$, and $n$ is a natural number with $n=k_0-1$; $\mathrm{par}_0\in\mathbb Z/2$ is a parity. The section $S$ on $2\times3$ real matrices is given explicitly by $S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)\,(M_{02}-iM_{12})^{n}\,\mathrm{gaussian}_3(M)$ with $\mathrm{gaussian}_3(M)=\exp(-\pi\sum_{i,b}M_{ib}^2)$.
--
--   Finally the branch is pinned to the weight-one principal Levi: $k_0=1$, $n=0$, $P_2=\mathrm{principal}(u_1,c_1,u_2,c_2)$ with $c_1\neq c_2$, and $\rho\in\mathbb C$ satisfies the two-sheet torus profile `hρ`: for every $b\in\mathbb Z/2$ and every $\tau>0$,
--   $$D.W(\operatorname{diag}(\tau,1))+(-1)^{b.\mathrm{val}}D.W(\operatorname{diag}(-\tau,1))=\rho\,\tau\cdot 4\int_{0}^{\infty}r^{\,u_1+\operatorname{signShift}(c_1+b)}e^{-\pi r^2}\,(\tau/r)^{\,u_2+\operatorname{signShift}(c_2+b)}e^{-\pi(\tau/r)^2}\,\frac{dr}{r}.$$
--
--   Under these hypotheses the conclusion asserts the existence of a real number $\sigma_2$ such that for every $s\in\mathbb C$ with $\operatorname{Re}s>\sigma_2$ the following identity holds. On the left stands the iterated integral over $a_2\in(0,\infty)$ and $a_1\in\mathbb R$ whose integrand is $0$ unless $a_1\neq0$ and $a_2>0$, in which case, with $q:=\mathrm{upperUnit}(a_1,0,a_2)=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}\in\mathrm{GL}_2(\mathbb R)$, it equals
--   $$\Bigl(|\det q|\;WA(\mathrm{par}_0)\bigl(w_0^R\cdot{}^{t}q^{-1}\bigr)\cdot \mathrm{dualWhittakerFn}_3\bigl(\mathrm{jacquetVector}_3\,D\,uR(w_0)\,aR(w_0)\,a\,\psi_\infty\,S\bigr)\bigl(\mathrm{archComponent}_3(\iota(\mathrm{archRealGLAt}(\text{default real place of }\mathbb Q)(q)))\bigr)\Bigr)\cdot|\det q|^{\,s-1/2}\cdot a_1^{-2},$$
--   where ${}^{t}q^{-1}$ is [`RSCarrier.transposeInv q`](def/LanglandsTunnell_RSCarrier.html#L31), $\mathrm{dualWhittakerFn}_3(W)(g)=W(\mathrm{longWeyl}_3\cdot{}^{t}g^{-1})$, $\mathrm{jacquetVector}_3$ is the quasi-character $\operatorname{quasiChar}(uR(w_0)+1,aR(w_0))$ of the determinant of the real matrix of $g$ times the integral over $e\in\mathbb R^{2\times2}$ of the Jacquet integrand built from $D$, $a$, $\psi_\infty$ and $S$, and $q$ is transported into $\mathrm{GL}_3$ of the infinite adeles of $\mathbb Q$ by the archimedean inclusion at the default place followed by the block embedding $\iota$ of $\mathrm{GL}_2$ into $\mathrm{GL}_3$ and projection to the archimedean component.
--
--   On the right stands the product of three factors. The first is $\varepsilon_\infty\,(-1)^{P.\mathrm{centralSign}.\mathrm{val}}\,(-1)^{r_2}$, where $\varepsilon_\infty=\operatorname{archRootNumber}$ of $K$ for the constant real parameter $w\mapsto P$ and the constant complex parameter $w\mapsto P.\mathrm{baseChange}$, twisted by $(uR,aR)$ at the real places and $(uC,kC)$ at the complex ones, i.e. the product of the epsilon factors of these twisted local parameters, and $r_2$ is the number of complex places of $K$. The second is the explicit constant $(-1)^{(aR(w_0)).\mathrm{val}+1}\,\frac{\pi}{2}\,\rho$. The third is the gamma factor of the dual parameters, namely the product over the multiset $\operatorname{twistedGammaR}$ of $K$ for the dual parameters $w\mapsto P^{\vee}$, the shifts $-uR$ and the parities $aR$ of $\Gamma_{\mathbb R}(s+\tfrac12+x)$, times the product over the multiset $\operatorname{twistedGammaC}$ of $K$ for the dual real parameters $w\mapsto P^\vee$, the dual complex parameters $w\mapsto (P.\mathrm{baseChange})^{\vee}$, and the data $-uR$, $aR$, $-uC$, $-kC$ of $\Gamma_{\mathbb C}(s+\tfrac12+y)$.
--
--   This is the dual (Weyl-translated) half of the archimedean Rankin–Selberg computation for the cubic induction step: it evaluates the folded torus integral of the conjugate-block section against the dual Whittaker vector on the weight-one principal Levi branch, producing the archimedean root number, an explicit constant $(-1)^{a_0+1}\pi\rho/2$, and the gamma factor attached to the dual archimedean parameters. It is used by [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3), where it is paired with the primal evaluation to supply the archimedean input to the functional equation required by the converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_weightOne_profile.lean

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

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell
open LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg
open LanglandsTunnell.CubicInduction
open LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_weightOne_profile
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
    (hk1 : k₀ = 1) (hn0 : n = 0)
    (u₁ u₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c₁ u₂ c₂) (hc : c₁ ≠ c₂)
    (ρ : ℂ)
    (hρ : ∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (u₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ))) :
    ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re →
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = ((archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) * (((-1 : ℂ) ^ ((aR w₀ h₀).val + 1) * ((Real.pi : ℂ) / 2)) * ρ)) * (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
                    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod) := by sorry
