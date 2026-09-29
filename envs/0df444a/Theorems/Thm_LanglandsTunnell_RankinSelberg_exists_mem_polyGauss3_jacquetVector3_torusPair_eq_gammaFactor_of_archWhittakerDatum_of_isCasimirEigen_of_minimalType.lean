-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_polyGauss3_jacquetVector3_torusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_minimalType
-- name    : LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_jacquetVector3_torusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_minimalType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/d354abf1-b229-518b-829b-a812b269d422
-- title:
--   Archimedean GL₂× GL₃ torus-pair Gamma identity, minimal type
-- statement:
--   The setting is that of the archimedean torus-pair computation for the cubic induction. Fixed are a number field $K$ with an integral algebra structure of $\mathcal O_{\mathbb Q}$ on $\mathcal O_K$, the hypothesis `_hdeg` that $[K:\mathbb Q]=3$, and a character $\mu\colon(\mathbb A_K)^\times\to\mathbb C^\times$ together with `_hμ`, asserting that $\mu$ is an admissible twist (trivial on principal ideles, continuous, and of absolute value $1$ everywhere). The hypothesis `_hns` excludes base change: there is no admissible twist $\eta$ of $\mathbb Q$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and whose trace $\mathfrak p=\mathfrak P\cap\mathcal O_{\mathbb Q}$ is unramified for $\eta$, the value $\mu(\text{uniformizer idele at }\mathfrak P)$ equals $\eta(\text{uniformizer idele at }\mathfrak p)^{f(\mathfrak P/\mathfrak p)}$, the exponent being the inertia degree.
--
--   The archimedean data of $\mu$ are recorded by families $uR$, $aR$ on the real places and $uC$, $kC$ on the complex places of $K$, with $uR\,w\in\mathbb C$, $aR\,w\in\mathbb Z/2$, $uC\,w\in\mathbb C$, $kC\,w\in\mathbb Z$; the hypotheses `huR`, `huC` say that for each real $w$ the local component of $\mu$ at $w$ is $x\mapsto \|x\|^{m_w u R\,w}(x/\|x\|)^{(aR\,w).\mathrm{val}}$ and for each complex $w$ it is $x\mapsto\|x\|^{m_w uC\,w}(x/\|x\|)^{kC\,w}$, $m_w$ denoting the multiplicity of $w$.
--
--   A character $\omega$ of $(\mathbb A_{\mathbb Q})^\times$ is fixed together with `hω`, a conjunction of three clauses: $\omega$ is an admissible twist of $\mathbb Q$; at every rational prime $p$ which is not a bad place for $(K,\mu)$ (that is, neither ramified in $K$ nor twist-ramified above $p$) $\omega$ is unramified and its Euler coefficient equals $-$ the coefficient of $T^3$ in the induced Euler polynomial of the coefficient system $\mathfrak P\mapsto\mu(\text{uniformizer at }\mathfrak P)$ (zero at ramified $\mathfrak P$); and, for every choice of archimedean data satisfying the two conditions above, the archimedean component of $\omega$ at the real place of $\mathbb Q$ has exponent $\sum_{w\text{ real}}uR\,w+\sum_{w\text{ complex}}2\,uC\,w$ and sign exponent $\sum_{w\text{ real}}(aR\,w).\mathrm{val}+\sum_{w\text{ complex}}(kC\,w+1)$.
--
--   Further fixed: a monoid homomorphism $E\colon(\mathbb A_{\mathbb Q,\infty})^\times\to(\mathbb A_{\mathbb Q})^\times$ with `hE` asserting that $E$ is a section of the infinite part whose finite part is trivial; a rational number $a$ with `ha` ($a\neq0$) and `ha1` ($a=-1$), an infinite idele $aInf$ with `haInf` representing $a$; an additive character $psiInf$ of $\mathbb A_{\mathbb Q,\infty}$ with `hpsiInf` identifying it with $x\mapsto\psi_{\mathrm{arch}}(ax)$; measurable and Borel structures on $\mathbb A_{\mathbb Q,\infty}$ and on its units; an additive measure $\nu_{\mathrm{add}}$ pinned by `hν_add` to $|a|^{1/2}$ times the push-forward of Lebesgue measure on the mixed space under the inverse of `InfiniteAdeleRing.ringEquiv_mixedSpace`; and a Haar measure $\nu_{\mathrm{mul}}$ on $(\mathbb A_{\mathbb Q,\infty})^\times$.
--
--   The abstract real $GL_2$ Whittaker datum consists of a real archimedean parameter $P$ (principal, given by $u_1,a_1,u_2,a_2$, or discrete, given by $u_0$ and $n\ge1$), the hypothesis `_hP₁` that in the principal case $|\mathrm{Re}(u_1-u_2)|<1$, a weight function $kw\colon\mathbb Z/2\to\mathrm{InfinitePlace}\,\mathbb Q\to\mathbb Z$, a torus function $Wr\colon\mathbb Z/2\to\mathrm{InfinitePlace}\,\mathbb Q\to\mathbb R\to\mathbb C$ and a function $WA\colon\mathbb Z/2\to GL_2(\mathbb R)\to\mathbb C$, subject to the following laws, one for each parity $par$ and each real place of $\mathbb Q$. `hkw1`: in the principal case $kw\,par\,w=\mathrm{signShift}(a_1+par)+\mathrm{signShift}(a_2+par)$, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$. `hkw2`: in the discrete case of parameter $n$, $kw\,par\,w=n+1$. `hWr1`: if $P$ is principal with $a_1=a_2$ and $par=a_1$ then $Wr\,par\,w(-t)=(-1)^{a_1.\mathrm{val}}Wr\,par\,w(t)$. `hWr2`: if $P$ is discrete then $Wr\,par\,w$ vanishes on the negative half-line. `hWr3`: if $P$ is principal with $a_1=a_2$ and $par=a_1+1$, then there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr\,par\,w(t)+(-1)^{a_1.\mathrm{val}}Wr\,par\,w(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$ at $s$. `hWr4`: for every $b$ with $b=par$ or $b=par+P.\mathrm{centralSign}$, the same Mellin transform (with $b$ in place of $a_1$) converges for $\mathrm{Re}\,s$ large and equals the archimedean factor of $P.\mathrm{twist}\,0\,b$ at $s$. `hWAN`: $WA\,par(n(x)h)=e^{-2\pi i a x}WA\,par(h)$ for the upper unipotent $n(x)$. `hWAZ`: $WA\,par(z\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}WA\,par(h)$ for scalar matrices. `hWAK`: $WA\,par(h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(kw\,par\,\mathrm{default})(\kappa)\,WA\,par(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`. `hWAt`: $WA\,par(\mathrm{diag}(t,1))=Wr\,par\,\mathrm{default}(t)$ for $t\in\mathbb R^\times$. `hWAc`: each $WA\,par$ is continuous. Finally $w_{0R}\in GL_2(\mathbb R)$ is pinned by `hw₀R` to the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   On the side of $K$, a real place $w_0$ with $h_0$ is fixed, together with a real archimedean parameter $P_2$ satisfying `hP₂`, which is the disjunction of two cases: either there are two further real places $w_1,w_2$, pairwise distinct from $w_0$ and from each other, exhausting all infinite places of $K$, with $P_2=\mathrm{principal}(uR\,w_1)(aR\,w_1)(uR\,w_2)(aR\,w_2)$; or there is a complex place $w_C$ such that the infinite places of $K$ are exactly $w_C$ and $w_0$, and either $kC\,w_C\neq0$ and $P_2=\mathrm{discrete}(uC\,w_C)\,|kC\,w_C|$, or $kC\,w_C=0$ and $P_2=\mathrm{principal}(uC\,w_C)\,0\,(uC\,w_C)\,1$. Fixed further are an archimedean datum $D$ of type $P_2$ (a Whittaker function $D.W$ on $2\times2$ real matrices with the smoothness, unipotent, central, zeta-integral, functional-equation, growth and decay laws of `ArchDatumR`) and an integer $k_0$, subject to: `hDW`, that $D.W(xr)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(r)\,D.W(x)$ for $r$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, that $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x\neq0$; `hDnz`, that $D.W$ is non-zero at some invertible matrix; and `hk₀min`, minimality of the weight: if $P_2$ is principal with signs $a_1,a_2$ then $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2$ in $\mathbb Z/2$, while if $P_2$ is discrete of parameter $m$ then $k_0=m+1$.
--
--   The conclusion asserts the existence of a polynomial-times-Gaussian datum $S$ in `polyGauss3`, i.e. a function on real $2\times3$ matrices of the form $M\mapsto p\big((M_{ij})\big)\cdot\mathrm{gaussian3}(M)$ for some polynomial $p$ in the six entries, such that, writing $W_S:=$ `jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) a psiInf S` for the associated function on $GL_3(\mathbb A_{\mathbb Q,\infty})$ — the quasicharacter $\mathrm{quasiChar}(uR\,w_0+1)(aR\,w_0)$ evaluated at the determinant of the real matrix of $g$, times the integral over $2\times2$ real matrices of `jacquetIntegrand3` — and $\iota(q):=$ `archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt … q))` for the archimedean component of the $GL_2\hookrightarrow GL_3$ image of $q\in GL_2(\mathbb R)$ at the real place of $\mathbb Q$, the following three assertions hold.
--
--   First, $W_S\neq0$ as a function on $GL_3(\mathbb A_{\mathbb Q,\infty})$. Secondly, there are an admissible twist $\sigma$ of $\mathbb Q$ and a complex number $s$ with `archZeta30` $\nu_{\mathrm{mul}}\,W_S\,(\sigma\circ E)\,s\,1\neq0$, that is $\int_{(\mathbb A_{\mathbb Q,\infty})^\times}W_S(\iota_{GL}(\mathrm{diag}(\alpha,1,1))\,)\,\sigma(E\alpha)\,\|\alpha\|^{s-1}\,d\nu_{\mathrm{mul}}(\alpha)\neq0$. Thirdly, there exist a parity $par_0\in\mathbb Z/2$, an abscissa $\sigma_a\in\mathbb R$ and non-zero constants $e,e^\vee$ with
--   $$e^\vee=\Big(\mathrm{archRootNumber}\,K\,(w\mapsto P)\,(w\mapsto P.\mathrm{baseChange})\,uR\,aR\,uC\,kC\cdot(-1)^{P.\mathrm{centralSign}.\mathrm{val}}\cdot(-1)^{\#\{w\ \text{complex}\}}\Big)\,e,$$
--   the root number being the product over the real places of $K$ of the epsilon factor of $P.\mathrm{twist}(uR\,w)(aR\,w)$ times the product over the complex places of the epsilon factor of $P.\mathrm{baseChange}.\mathrm{twist}(uC\,w)(kC\,w)$, such that four statements hold.
--
--   (a) For every $k$ in `rowIsometrySubgroup ℝ` (the $k\in GL_2(\mathbb R)$ with $|\det k|=1$ preserving the quadratic form $\|xk_{00}+yk_{10}\|^2+\|xk_{01}+yk_{11}\|^2=\|x\|^2+\|y\|^2$) with $\det k=1$, and every $q\in GL_2(\mathbb R)$: $WA\,par_0(qk)\,W_S(\iota(qk))=WA\,par_0(q)\,W_S(\iota(q))$.
--
--   (b) For every such $k$ and every $q$: $|\det(qk)|\,WA\,par_0\big(w_{0R}\cdot{}^t(qk)^{-1}\big)\cdot \widetilde W_S(\iota(qk))=|\det q|\,WA\,par_0\big(w_{0R}\cdot{}^tq^{-1}\big)\cdot\widetilde W_S(\iota(q))$, where $\widetilde W_S=$ `dualWhittakerFn3` $W_S$ is $g\mapsto W_S(\mathrm{longWeyl}_3\cdot{}^tg^{-1})$ and [`RSCarrier.transposeInv`](def/LanglandsTunnell_RSCarrier.html#L31) is $q\mapsto{}^t(q^{-1})$.
--
--   (c) For every $s$ with $\sigma_a<\mathrm{Re}\,s$, the iterated integral over $a_2\in(0,\infty)$ and $a_1\in\mathbb R$ of the integrand which, for $a_1\neq0$ and $a_2>0$ and with $q=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$ (the matrix `upperUnit a₁ 0 a₂`), equals $\big(WA\,par_0(q)\,W_S(\iota(q))\big)\,|\det q|^{s-1/2}\,a_1^{-2}$, and vanishes otherwise, equals
--   $$e\cdot\prod_{x\in\Gamma_{\mathbb R}}\Gamma_{\mathbb R}\!\left(s+\tfrac12+x\right)\cdot\prod_{x\in\Gamma_{\mathbb C}}\Gamma_{\mathbb C}\!\left(s+\tfrac12+x\right),$$
--   where $\Gamma_{\mathbb R}$ is the multiset `twistedGammaR K (archOfParamR K P) uR aR`, the sum over the real places $w$ of $K$ of the real Gamma shifts of $P.\mathrm{twist}(uR\,w)(aR\,w)$, and $\Gamma_{\mathbb C}$ is `twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC`, the sum of the complex Gamma shifts of $P.\mathrm{twist}(uR\,w)(aR\,w)$ over the real places and of $P.\mathrm{baseChange}.\mathrm{twist}(uC\,w)(kC\,w)$ over the complex places.
--
--   (d) For every $s$ with $\sigma_a<\mathrm{Re}\,s$, the same iterated integral with integrand $\big(|\det q|\,WA\,par_0(w_{0R}\cdot{}^tq^{-1})\cdot\widetilde W_S(\iota(q))\big)\,|\det q|^{s-1/2}\,a_1^{-2}$ (again zero unless $a_1\neq0$ and $a_2>0$) equals $e^\vee$ times the corresponding product of $\Gamma_{\mathbb R}(s+\tfrac12+x)$ and $\Gamma_{\mathbb C}(s+\tfrac12+x)$ formed from the dual data, namely `twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR` and `twistedGammaC K` with the dualised real and complex parameters and the families $-uR$, $aR$, $-uC$, $-kC$.
--
--   This is the archimedean local input of the $GL_2\times GL_3$ Rankin–Selberg computation in the cubic induction: for a minimal $SO(2)$-type Casimir eigendatum $D$ at the places of $K$ other than a chosen real place $w_0$, it produces a polynomial-times-Gaussian Schwartz datum whose Jacquet–Whittaker vector on $GL_3(\mathbb R)$ pairs with the abstract $GL_2$ Whittaker datum to give exactly the expected archimedean Gamma factor, with the dual integral differing by the archimedean root number. It is used by [`LanglandsTunnell.RankinSelberg.exists_archWhittaker_torusPair_eq_gammaFactor_of_archWhittakerDatum`](thm.html#LanglandsTunnell.RankinSelberg.exists_archWhittaker_torusPair_eq_gammaFactor_of_archWhittakerDatum), which feeds the archimedean functional equation into the converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_mem_polyGauss3_jacquetVector3_torusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_minimalType.lean

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
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda MeasureTheory
open LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_jacquetVector3_torusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_minimalType
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
      (∀ (u : ℂ) (m : ℕ) (hm : 1 ≤ m), P₂ = RealArchParam.discrete u m hm → k₀ = (m : ℤ) + 1)) :
    ∃ S ∈ polyGauss3, (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) ≠ 0 ∧
      (∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (σ.comp E) s 1 ≠ 0) ∧
      ∃ (par₀ : ZMod 2) (σa : ℝ) (e ed : ℂ), e ≠ 0 ∧ ed ≠ 0 ∧
        ed = (archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) * e ∧
        (∀ k ∈ AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 → ∀ q : GL (Fin 2) ℝ,
            WA par₀ (q * k) * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (q * k))))
              = WA par₀ q * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) ∧
        (∀ k ∈ AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 → ∀ q : GL (Fin 2) ℝ,
            ((((|(Matrix.GeneralLinearGroup.det (q * k) : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv (q * k))) *
                dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (q * k)))))
              = ((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) *
                dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q))))) ∧
        (∀ s : ℂ, σa < s.re →
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                ((WA par₀ q * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = e * (((twistedGammaR K (archOfParamR K P) uR aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) ∧
        (∀ s : ℂ, σa < s.re →
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = ed * (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
                    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) := by sorry
