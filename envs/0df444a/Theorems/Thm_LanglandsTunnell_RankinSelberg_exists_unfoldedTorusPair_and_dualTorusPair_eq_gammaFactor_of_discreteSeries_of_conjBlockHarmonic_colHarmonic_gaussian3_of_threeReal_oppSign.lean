-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_threeReal_oppSign
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_threeReal_oppSign
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/e7f1393e-d634-5373-b691-0ad81390eb95
-- title:
--   Primal and dual torus pairs: three real places, opposite signs
-- statement:
--   Throughout, $K$ is a number field of degree $3$ over $\mathbb{Q}$ whose ring of integers is an integral extension of $\mathbb{Z}=\mathcal{O}_{\mathbb{Q}}$, and $\mu\colon (\mathbb{A}_K)^{\times}\to\mathbb{C}^{\times}$ is a character which is *admissible* in the sense of `IsAdmissibleTwist`: it is trivial on $K^{\times}$, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` excludes that $\mu$ comes from $\mathbb{Q}$: there is no admissible character $\eta$ of $(\mathbb{A}_{\mathbb{Q}})^{\times}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose underlying prime $p$ of $\mathbb{Z}$ is unramified for $\eta$, the value of $\mu$ on the uniformiser idele at $\mathfrak{P}$ equals the value of $\eta$ on the uniformiser idele at $p$ raised to the inertia degree of $\mathfrak{P}$ over $p$.
--
--   The archimedean data of $\mu$ are recorded by functions $uR,aR$ on the real places and $uC,kC$ on the complex places of $K$, with values in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$ respectively; the hypotheses `huR` and `huC` say that at each real place $w$ the local component of $\mu$ is $x\mapsto \lVert x\rVert^{\,m_w\,uR(w)}\,(x/\lVert x\rVert)^{aR(w)}$ and at each complex place $w$ it is $x\mapsto\lVert x\rVert^{\,m_w\,uC(w)}(x/\lVert x\rVert)^{kC(w)}$, in the sense of `IsArchCompAt`.
--
--   A character $\omega$ of $(\mathbb{A}_{\mathbb{Q}})^{\times}$ is given together with the three-clause hypothesis `hω`: $\omega$ is admissible; at every prime $p$ of $\mathbb{Z}$ which is neither ramified in $K$ nor twist-ramified for $\mu$ (i.e. `¬ IsBadPlace K μ p`), $\omega$ is unramified and its Euler coefficient is $-$ the degree-$3$ coefficient of the induced Euler polynomial formed from the unramified coefficients $\mathrm{inducedCoeff}\,K\,\mu$; and, for every choice of archimedean data satisfying the two `IsArchCompAt` conditions above, at the real place of $\mathbb{Q}$ the component of $\omega$ has exponent $\sum_w uR(w)+\sum_w 2\,uC(w)$ and integer parameter $\sum_w aR(w)+\sum_w\bigl(kC(w)+1\bigr)$, the sums being over the real, respectively complex, places of $K$.
--
--   Further global data: a monoid homomorphism $E$ from $(\mathbb{A}_{\mathbb{Q},\infty})^{\times}$ to $(\mathbb{A}_{\mathbb{Q}})^{\times}$ splitting the archimedean ideles (`hE`: infinite part of $E(u)$ is $u$, finite part is $1$); a rational number $a$ with $a\neq 0$ and $a=-1$, together with an archimedean idele unit $aInf$ whose underlying element is the image of $a$; an additive character $\psi_{\infty}$ of $\mathbb{A}_{\mathbb{Q},\infty}$ equal to the standard archimedean character `psiArch` shifted by $a$; measurable-space and Borel assumptions on $\mathbb{A}_{\mathbb{Q},\infty}$ and its units; an additive measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the pushforward of Lebesgue measure along the inverse of the mixed-space identification of $\mathbb{A}_{\mathbb{Q},\infty}$; and a Haar measure $\nu_{\mathrm{mul}}$ on $(\mathbb{A}_{\mathbb{Q},\infty})^{\times}$.
--
--   The $\mathrm{GL}_2$ archimedean parameter is a `RealArchParam` $P$ subject to `_hP₁` (in the principal case $|\mathrm{Re}(u_1-u_2)|<1$), accompanied by a weight function $kw$, a torus profile $Wr$ and a group function $WA$, each indexed by a parity $par\in\mathbb{Z}/2$. Their hypotheses are: `hkw1`, in the principal case $kw(par,w)=\mathrm{signShift}(a_1+par)+\mathrm{signShift}(a_2+par)$, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$; `hkw2`, in the discrete case $P=\mathrm{discrete}(u_0,n)$ one has $kw(par,w)=n+1$; `hWr1`, in the principal case with equal signs $a_1=a_2$ and $par=a_1$, $Wr(par,w,-t)=(-1)^{a_1}Wr(par,w,t)$; `hWr2`, in the discrete case $Wr(par,w,t)=0$ for $t<0$; `hWr3`, in the principal case with $a_1=a_2$ and $par=a_1+1$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto\bigl(Wr(par,w,t)+(-1)^{a_1}Wr(par,w,-t)\bigr)/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$; `hWr4`, for every $b$ with $b=par$ or $b=par+\mathrm{centralSign}(P)$ there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ that same Mellin transform converges and equals the archimedean factor of $P$ twisted by $(0,b)$. For $WA$: `hWAN` gives the unipotent law $WA(par,u(x)h)=e^{-2\pi i a x}WA(par,h)$; `hWAZ` the central law $WA(par,zh)=|z|^{\mathrm{centralExponent}(P)+1}(z/|z|)^{\mathrm{centralSign}(P)}WA(par,h)$; `hWAK` right equivariance $WA(par,h\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}\bigl(kw(par,\ast)\bigr)(\kappa)\,WA(par,h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`, the weight being evaluated at the unique infinite place of $\mathbb{Q}$; `hWAt` compatibility $WA(par,\mathrm{diag}(t,1))=Wr(par,\ast,t)$; and `hWAc` continuity of each $WA(par,\cdot)$. Finally $w_{0R}\in\mathrm{GL}_2(\mathbb{R})$ is the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   The Levi data consist of a real place $w_0$ of $K$, a second `RealArchParam` $P_2$ subject to the four-branch disjunction `hP₂` (either $K$ has three real places $w_0,w_1,w_2$ and $P_2$ is the principal parameter built from $(uR,aR)$ at $w_1,w_2$, or $K$ has one complex place $w_C$ besides $w_0$ and $P_2$ is either $\mathrm{discrete}(uC(w_C),|kC(w_C)|)$ when $kC(w_C)\neq 0$, or $\mathrm{principal}(uC(w_C),0,uC(w_C),1)$ when $kC(w_C)=0$), an archimedean datum $D$ of type `ArchDatumR P₂`, and an integer $k_0$ with: `hDW`, $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, $D$ is a Casimir eigenfunction, i.e. $\mathrm{matrixCasimir}(D.W)(x)=\mathrm{laplaceEigenvalue}(P_2)\,D.W(x)$ for every invertible $x$; `hDnz`, $D.W$ is not identically zero; and `hk₀min`, asserting that in the principal case $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \pmod 2$, and in the discrete case with parameter $m$ that $k_0=m+1$.
--
--   The discrete-series specialisation is `hPdisc`: $P=\mathrm{discrete}(u_P,n_P)$ with $1\le n_P$; consequently the clauses of `_hP₁`, `hkw1`, `hWr1` and `hWr3`, which are conditioned on $P$ being principal, are vacuous. Put $m=n_P+1$ (`hm`). Natural numbers $n$ and a real $\varepsilon'$ satisfy `hcol`: either $\varepsilon'=-1$ and $n=k_0-m$, or $\varepsilon'=1$ and $n=m-k_0$. A parity $par_0\in\mathbb{Z}/2$ is fixed, and the flat section $S$ on real $2\times 3$ matrices is prescribed by `hS`:
--   $$S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^{m}\,\bigl(M_{02}+\varepsilon' i M_{12}\bigr)^{n}\,\exp\Bigl(-\pi\textstyle\sum_{i,b}M_{ib}^2\Bigr).$$
--   The torus profile at parity $par_0$ and the unique infinite place of $\mathbb{Q}$ is prescribed explicitly: $Wr(par_0,\ast,t)=2\,t^{\,u_P+n_P/2+1}e^{-2\pi t}$ for $t>0$ (`hWpos`) and $Wr(par_0,\ast,t)=0$ for $t<0$ (`hWneg`).
--
--   This statement is the branch of the four in `hP₂` in which $K$ has three real places: real places $w_1,w_2$ with $w_0,w_1,w_2$ pairwise distinct (`h01`, `h02`, `h12`) and exhausting the infinite places of $K$ (`hall`), $P_2=\mathrm{principal}\bigl(uR(w_1),aR(w_1),uR(w_2),aR(w_2)\bigr)$ (`hP₂eq`), and the opposite-sign condition `hc`: $aR(w_1)\neq aR(w_2)$. Together with `hk₀min` this forces $k_0=1$, and then, $m=n_P+1\ge 2$ being at least $2$, the first alternative of `hcol` is impossible, so $\varepsilon'=1$ and $n=m-1$.
--
--   The conclusion asserts the existence of a real abscissa $\sigma_a$ and a complex number $e\neq 0$ such that the following two identities hold.
--
--   First, for every $s$ with $\mathrm{Re}\,s>\sigma_a$, the integral over real $2\times 2$ matrices $\eta$ (the integration variable is also called `e` in the Lean text) of
--   $$\mathrm{quasiChar}\bigl(uR(w_0)+2,\,aR(w_0)\bigr)(\det\eta)\cdot|\det\eta|^{-2}\cdot\Bigl(\int_{\mathbb{R}}Wr(par_0,\ast,t)\,D.W\bigl(\mathrm{diag}(at,1)\,\eta^{-1}\bigr)\,|t|^{\,s-1/2}\,t^{-2}\,dt\Bigr)\cdot\Bigl(\int_{0}^{\infty}y^{\,\mathrm{centralExponent}(P)+\mathrm{centralExponent}(P_2)+2s}\,\mathrm{godementInner3}\bigl(\psi_{\infty}\!\cdot\!y,\,S,\,\eta,\,1\bigr)\,dy\Bigr)$$
--   equals $e$ times the product of $\Gamma_{\mathbb{R}}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGammaR}$ of $K$ formed from the constant parameter $P$ and the data $(uR,aR)$, times the product of $\Gamma_{\mathbb{C}}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGammaC}$ formed from the constant parameters $P$ at the real places and $P.\mathrm{baseChange}$ at the complex places, twisted by $(uR,aR)$ and $(uC,kC)$. Here $\mathrm{quasiChar}(u,a)(y)=|y|^{u}$ if $a=0$ and $|y|^{u}\mathrm{sgn}(y)$ otherwise; $\mathrm{centralExponent}(P)=2u_P$ and $\mathrm{centralExponent}(P_2)=uR(w_1)+uR(w_2)$; $\psi_{\infty}\!\cdot\!y$ denotes the character $\psi_{\infty}$ shifted by the image of $y$ under `StandardKernel.ofReal`; and $\mathrm{godementInner3}(\psi,S,h,\mathbf 1)$ is the integral over $v\in\mathbb{R}^2$ of $S$ evaluated at $h$ times the matrix with rows $m_0+v_0m_2$, $m_1+v_1m_2$ (for $m=\mathbf 1$), against $\psi$ of the image of $-v_1$.
--
--   Second, for every $s$ with $\mathrm{Re}\,s>\sigma_a$, the iterated integral over $a_2\in(0,\infty)$ and $a_1\in\mathbb{R}$ of the integrand which, when $a_1\neq 0$ and $a_2>0$, is formed from $q=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}\in\mathrm{GL}_2(\mathbb{R})$ as
--   $$|\det q|\cdot WA\bigl(par_0,\,w_{0R}\cdot{}^{t}q^{-1}\bigr)\cdot \mathrm{dualWhittakerFn3}\bigl(\mathrm{jacquetVector3}\,D\,uR(w_0)\,aR(w_0)\,a\,\psi_{\infty}\,S\bigr)\bigl(\text{the archimedean component of the image of }q\bigr)\cdot|\det q|^{\,s-1/2}\cdot a_1^{-2},$$
--   and is $0$ otherwise, equals
--   $$\Bigl(\mathrm{archRootNumber}\,K\,P\,P.\mathrm{baseChange}\,uR\,aR\,uC\,kC\cdot(-1)^{\mathrm{centralSign}(P)}\cdot(-1)^{\#\{\text{complex places of }K\}}\Bigr)\cdot e$$
--   times the product of $\Gamma_{\mathbb{R}}(s+\tfrac12+x)$ over $\mathrm{twistedGammaR}$ of the dual parameter $P^{\vee}$ with data $(-uR,aR)$, times the product of $\Gamma_{\mathbb{C}}(s+\tfrac12+x)$ over $\mathrm{twistedGammaC}$ of the dual parameters $P^{\vee}$ and $(P.\mathrm{baseChange})^{\vee}$ with data $(-uR,aR)$ and $(-uC,-kC)$. Here ${}^{t}q^{-1}$ is [`RSCarrier.transposeInv`](def/LanglandsTunnell_RSCarrier.html#L31); $\mathrm{dualWhittakerFn3}(W)(g)=W(w_3\,{}^{t}g^{-1})$ with $w_3$ the long Weyl element of $\mathrm{GL}_3$; $\mathrm{jacquetVector3}$ is the quasicharacter $\mathrm{quasiChar}(uR(w_0)+1,aR(w_0))$ of the determinant of the real matrix of $g$ times the integral over real $2\times2$ matrices of the Jacquet integrand attached to $D$, $a$, $\psi_\infty$ and $S$; the argument of $\mathrm{dualWhittakerFn3}$ is the archimedean $\mathrm{GL}_3$ component of the image of $q$ under the embedding of $\mathrm{GL}_2(\mathbb{R})$ at the real place of $\mathbb{Q}$ followed by $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$; and $\mathrm{archRootNumber}$ is the product of the archimedean epsilon factors of the twisted parameters over all infinite places of $K$. The same $\sigma_a$ and the same nonzero constant $e$ occur in both identities.
--
--   This is the archimedean Rankin–Selberg computation for the $\mathrm{GL}_3\times\mathrm{GL}_2$ pair arising in the Langlands–Tunnell converse-theorem argument, in the case of a discrete-series $\mathrm{GL}_2$ parameter and the Levi branch where the cubic field has three real places with opposite signs at $w_1,w_2$: the unfolded primal and dual torus integrals are identified, up to one and the same nonzero constant and the archimedean root number, with the twisted $\Gamma$-products of the induced parameter and of its dual. It is one of the branch cases assembled by [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3), whose hypothesis on $P_2$ is the disjunction of the four possible branch data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_threeReal_oppSign.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_threeReal_oppSign
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
    (uP : ℂ) (nP : ℕ) (hnP : 1 ≤ nP) (hPdisc : P = RealArchParam.discrete uP nP hnP)
    (m : ℕ) (hm : m = nP + 1)
    (n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (hWpos : ∀ t : ℝ, 0 < t → Wr par₀ default t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → Wr par₀ default t = 0)
    (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal)
    (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h12 : w₁ ≠ w₂) (hall : ∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂)
    (hP₂eq : P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂))
    (hc : aR w₁ h₁ ≠ aR w₂ h₂) :
        ∃ (σa : ℝ) (e : ℂ), e ≠ 0 ∧
        (∀ s : ℂ, σa < s.re →
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
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
              = ((archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) * e) * (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
                    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) := by sorry
