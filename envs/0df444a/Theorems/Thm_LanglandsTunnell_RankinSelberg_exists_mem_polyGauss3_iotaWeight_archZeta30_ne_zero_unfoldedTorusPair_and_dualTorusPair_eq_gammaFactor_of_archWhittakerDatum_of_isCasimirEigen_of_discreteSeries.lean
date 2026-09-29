-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_discreteSeries
-- name    : LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_discreteSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/af39846e-9468-587b-9b17-f8845c344479
-- title:
--   Archimedean GL₃× GL₂ pair identity: discrete-series case
-- statement:
--   Throughout, $K$ is a number field which is an $\mathcal O_{\mathbb Q}$-algebra integral over $\mathcal O_{\mathbb Q}$ and whose degree over $\mathbb Q$ is $3$ (`_hdeg`), and $\mu$ is a homomorphism from the ideles of $K$ to $\mathbb C^\times$ which is an admissible twist (`_hμ`), i.e. trivial on principal ideles, continuous and unitary. The hypothesis `_hns` asserts that $\mu$ is not a base change: there is no admissible twist $\eta$ of $\mathbb Q$ such that, at every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and lying over a prime at which $\eta$ is unramified, $\mu$ of a uniformiser idele at $\mathfrak P$ equals $\eta$ of a uniformiser idele at $\mathfrak P\cap\mathcal O_{\mathbb Q}$ raised to the inertia degree of $\mathfrak P$.
--
--   The archimedean components of $\mu$ are described by functions $uR,aR$ on the real places and $uC,kC$ on the complex places of $K$: by `huR` and `huC`, the local component of $\mu$ at a real place $w$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,uR(w)}(x/\|x\|)^{aR(w)}$ (with the exponent the representative in $\{0,1\}$ of $aR(w)\in\mathbb Z/2$), and at a complex place $w$ it is $x\mapsto\|x\|^{\mathrm{mult}(w)\,uC(w)}(x/\|x\|)^{kC(w)}$.
--
--   The character $\omega$ of the ideles of $\mathbb Q$ plays the role of the central character of the induced datum: the hypothesis `hω` has three clauses, requiring that $\omega$ be an admissible twist of $\mathbb Q$; that at every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not bad for $(K,\mu)$ — that is, $p$ is unramified in $K$ and $\mu$ is not twist-ramified above $p$ — the character $\omega$ be unramified at $p$ with Euler coefficient $\omega(\varpi_p)$ equal to $\mathrm{inducedE3}$ of the unramified Frobenius values of $\mu$, namely minus the degree-$3$ coefficient of the induced Euler polynomial at $p$; and that for every choice of archimedean data $uR,aR,uC,kC$ satisfying the two conditions above, the component of $\omega$ at the real place of $\mathbb Q$ be given by the exponent $\sum_{w\ \mathrm{real}}uR(w)+\sum_{w\ \mathrm{complex}}2\,uC(w)$ and the integer $\sum_{w\ \mathrm{real}}aR(w)+\sum_{w\ \mathrm{complex}}(kC(w)+1)$.
--
--   Further global data: $E$ is a homomorphism from the units of the infinite adeles of $\mathbb Q$ to the ideles, splitting the projection in the sense of `hE` (infinite part of $E(u)$ equal to $u$, finite part equal to $1$); $a$ is a nonzero rational with $a=-1$ (`ha`, `ha1`), $a_\infty$ an infinite idele unit whose underlying infinite adele is the image of $a$ (`haInf`), and $\psi_\infty$ the additive character $x\mapsto \psi_{\mathrm{arch}}(a\,x)$ of the infinite adeles (`hpsiInf`). Measurable and Borel structures on the infinite adeles and their units are fixed; $\nu_{\mathrm{add}}$ is the measure obtained by scaling the transport of Lebesgue measure from the mixed space by $|a|^{1/2}$ (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the units of the infinite adeles.
--
--   The $GL_2$ archimedean parameter is $P:\mathrm{RealArchParam}$, subject to `_hP₁`: if $P$ is principal with exponents $u_1,u_2$ then $|\mathrm{Re}(u_1-u_2)|<1$. Attached to $P$ are a weight function $kw:\mathbb Z/2\to\mathrm{InfinitePlace}(\mathbb Q)\to\mathbb Z$, a torus function $Wr:\mathbb Z/2\to\mathrm{InfinitePlace}(\mathbb Q)\to\mathbb C\to\mathbb C$ and a Whittaker function $WA:\mathbb Z/2\to GL_2(\mathbb R)\to\mathbb C$, one for each parity, constrained as follows. The weight clauses: `hkw1` says that in the principal case $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ one has $kw(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ at every real place $w$ of $\mathbb Q$, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$; `hkw2` says that in the discrete case $P=\mathrm{discrete}(u_0,n)$ with $n\ge1$ one has $kw(\mathrm{par},w)=n+1$. The torus clauses: `hWr1` gives, in a principal case with equal parities $a_1=a_2$ and $\mathrm{par}=a_1$, the symmetry $Wr(\mathrm{par},w,-t)=(-1)^{a_1}Wr(\mathrm{par},w,t)$; `hWr2` gives, in the discrete case, that $Wr(\mathrm{par},w,t)=0$ for $t<0$; `hWr3` gives, in a principal case with $a_1=a_2$ and $\mathrm{par}=a_1+1$, an abscissa $s_0$ beyond which the Mellin transform of $t\mapsto (Wr(\mathrm{par},w,t)+(-1)^{a_1}Wr(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$; and `hWr4` gives, for every $b\in\mathbb Z/2$ with $b=\mathrm{par}$ or $b=\mathrm{par}+P.\mathrm{centralSign}$, an abscissa beyond which the same Mellin transform, formed with $(-1)^{b}$, converges and equals the archimedean factor of $P$ twisted by $(0,b)$. The group-theoretic clauses on $WA$: `hWAN` is the unipotent law $WA(\mathrm{par},n(x)h)=\exp(-2\pi i a x)\,WA(\mathrm{par},h)$; `hWAZ` is the central law $WA(\mathrm{par},z\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}}WA(\mathrm{par},h)$ for scalar $z$; `hWAK` is the right weight law $WA(\mathrm{par},h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(kw(\mathrm{par},\ast))(\kappa)\,WA(\mathrm{par},h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt` identifies $WA(\mathrm{par},\mathrm{diag}(t,1))$ with $Wr(\mathrm{par},\ast,t)$ for $t\in\mathbb R^\times$; and `hWAc` asserts continuity of each $WA(\mathrm{par},\cdot)$. Finally $w_{0,\mathbb R}\in GL_2(\mathbb R)$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀R`).
--
--   On the side of $K$, $w_0$ is a real place of $K$, and $P_2$ is a real archimedean parameter tied to the remaining archimedean data by `hP₂`: either $K$ has exactly the three real places $w_0,w_1,w_2$ and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$, or $K$ has exactly one complex place $w_C$ besides $w_0$ and then $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$ if $kC(w_C)\neq0$, while if $kC(w_C)=0$ then $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$. The datum $D:\mathrm{ArchDatumR}\,P_2$ packages a Whittaker function $D.W$ on $2\times2$ real matrices for the parameter $P_2$ together with its unipotent and central transformation laws, entire completed zeta integrals with the local functional equation and epsilon factor of $P_2$, and growth and decay estimates. An integer $k_0$ is given with: `hDW`, the right weight law $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, that $D$ is a Casimir eigenvector, i.e. $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for every $x$ of nonzero determinant; `hDnz`, that $D.W$ does not vanish identically on $GL_2(\mathbb R)$; and `hk₀min`, the minimality of the weight: in the principal case $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \pmod 2$, and in the discrete case of weight $m$ one has $k_0=m+1$. The last hypothesis `hPdisc` is the discrete-series assumption on the $GL_2$ parameter: $P=\mathrm{discrete}(u,n)$ for some $u\in\mathbb C$ and $n\ge1$.
--
--   Under these assumptions there exist a parity $\mathrm{par}_0\in\mathbb Z/2$ and a Schwartz function $S$ in `polyGauss3`, that is, a function on $2\times3$ real matrices of the form (a polynomial in the entries, with complex coefficients) times `gaussian3`, such that the following four assertions hold for the Jacquet vector $J:=\mathrm{jacquetVector3}\,D\,(uR(w_0))\,(aR(w_0))\,a\,\psi_\infty\,S$ on $GL_3$ of the infinite adeles of $\mathbb Q$, whose value at $g$ is $\mathrm{quasiChar}(uR(w_0)+1,aR(w_0))(\det g)$ times the integral over $2\times2$ real matrices of `jacquetIntegrand3`.
--
--   First, the weight law: for every $\kappa$ in `rowIsometrySubgroup₀ ℝ` and every $g\in GL_3$ of the infinite adeles,
--   $$J\bigl(g\cdot \iota(\kappa)\bigr)=\mathrm{archWeightChar}_{\mathbb R}\bigl(kw(\mathrm{par}_0,\ast)\bigr)(\kappa)^{-1}\,J(g),$$
--   where $\iota(\kappa)$ denotes the image of $\kappa$ under the inclusion of $GL_2(\mathbb R)$ at the real place of $\mathbb Q$, followed by the embedding of $GL_2$ into $GL_3$ of the ideles and by the archimedean component map.
--
--   Secondly, non-vanishing of the archimedean $GL_3\times GL_1$ zeta integral: there exist an admissible twist $\sigma$ of $\mathbb Q$ and a complex $s$ with
--   $$\mathrm{archZeta30}\,\nu_{\mathrm{mul}}\,J\,(\sigma\circ E)\,s\,1=\int J\bigl(\iota(\mathrm{diag}(\alpha,1))\bigr)\,\sigma(E\alpha)\,\|\alpha\|^{s-1}\,d\nu_{\mathrm{mul}}(\alpha)\neq0 .$$
--
--   Thirdly, there exist an abscissa $\sigma_a\in\mathbb R$ and a nonzero constant $e\in\mathbb C$ such that two integral identities hold for all $s$ with $\mathrm{Re}\,s>\sigma_a$. The primal (unfolded) torus pair: the integral over $2\times2$ real matrices $h$ (the integration variable carries the name `e` in the Lean text) of
--   $$\mathrm{quasiChar}\bigl(uR(w_0)+2,aR(w_0)\bigr)(\det h)\cdot|\det h|^{-2}\cdot\Bigl(\int_{\mathbb R} Wr(\mathrm{par}_0,\ast,t)\,D.W\bigl(\mathrm{diag}(a t,1)\,h^{-1}\bigr)|t|^{s-1/2}t^{-2}\,dt\Bigr)\cdot\Bigl(\int_0^\infty y^{P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,\mathrm{godementInner3}\bigl(\psi_\infty(\,\cdot\,y),S,h,1\bigr)\,dy\Bigr)$$
--   equals $e$ times the product of $\Gamma_{\mathbb R}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGammaR}\,K$ formed from the constant parameter $P$ at the real places and the twists $(uR,aR)$, times the product of $\Gamma_{\mathbb C}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGammaC}\,K$ formed from $P$ at the real places, its base change $P.\mathrm{baseChange}$ at the complex places, and the twists $(uR,aR)$ and $(uC,kC)$. Here $\mathrm{godementInner3}(\psi,S,h,m)$ is $\int_{\mathbb R^2}S\bigl(h\cdot(\text{rows }m_0+v_0m_2,\ m_1+v_1m_2)\bigr)\psi(-v_1)\,dv$.
--
--   The dual torus pair: the iterated integral over $a_2>0$ and $a_1\in\mathbb R$ of the integrand which, when $a_1\neq0$ and $a_2>0$, is obtained from $q:=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}\in GL_2(\mathbb R)$ as
--   $$|\det q|\;WA\bigl(\mathrm{par}_0,\;w_{0,\mathbb R}\,(q^{-1})^{\mathrm{T}}\bigr)\cdot \bigl(\mathrm{dualWhittakerFn3}\,J\bigr)\bigl(\iota(q)\bigr)\cdot|\det q|^{s-1/2}\cdot a_1^{-2},$$
--   and is $0$ otherwise, where $\mathrm{dualWhittakerFn3}\,J$ at $g$ is $J(\mathrm{longWeyl3}\cdot(g^{-1})^{\mathrm{T}})$ and $\iota(q)$ is again the image of $q$ in $GL_3$ of the infinite adeles, equals
--   $$\Bigl(\mathrm{archRootNumber}\,K\,\cdot(-1)^{P.\mathrm{centralSign}}\cdot(-1)^{r_2}\Bigr)\,e\;\cdot\;\prod\Gamma_{\mathbb R}\bigl(s+\tfrac12+x\bigr)\prod\Gamma_{\mathbb C}\bigl(s+\tfrac12+x\bigr),$$
--   where $r_2$ is the number of complex places of $K$, the root number is the product over the real places of the epsilon factors of $P$ twisted by $(uR,aR)$ times the product over the complex places of the epsilon factors of $P.\mathrm{baseChange}$ twisted by $(uC,kC)$, and the two Gamma products are now taken over the multisets $\mathrm{twistedGammaR}$ and $\mathrm{twistedGammaC}$ formed from the dual parameters $P^{\vee}$ at the real places and $(P.\mathrm{baseChange})^{\vee}$ at the complex places, with the twists $(-uR,aR)$ and $(-uC,-kC)$.
--
--   This is the archimedean Rankin–Selberg computation for the pair consisting of the cubic automorphic induction of $\mu$ and a $GL_2$ parameter $P$, in the case where $P$ is a discrete series: it produces a polynomial-times-Gaussian Schwartz datum whose Jacquet vector has the prescribed $SO_2$-weight, a non-vanishing archimedean $GL_3\times GL_1$ zeta integral, and primal and dual torus integrals equal to the expected products of $\Gamma_{\mathbb R}$- and $\Gamma_{\mathbb C}$-factors with the archimedean root number. It feeds the local archimedean input of the $GL_3$ converse theorem used in the Langlands–Tunnell step, and is cited by the companion statement in which the discrete-series hypothesis on $P$ is replaced by the hypothesis that $P$ is not of weight one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_discreteSeries.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_discreteSeries
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
    (hPdisc : ∃ (u : ℂ) (n : ℕ) (hn : 1 ≤ n), P = RealArchParam.discrete u n hn) :
    ∃ (par₀ : ZMod 2), ∃ S ∈ polyGauss3,
        (∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
            (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (g * (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) κ))))
              = ((archWeightCharℝ (kw par₀ default) ⟨κ, hκ⟩ : ℂ))⁻¹ * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) g) ∧
        (∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (σ.comp E) s 1 ≠ 0) ∧
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
