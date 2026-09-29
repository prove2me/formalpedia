-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_minorSection_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_minorSection_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/88747a72-83b2-54a4-94c9-fcf444dd1837
-- title:
--   Dual torus pair of the minor-section Jacquet vector, unfolded
-- statement:
--   Throughout, $K$ is a field carrying a number-field structure, with $\mathcal O_K$ an integral $\mathcal O_{\mathbb Q}$-algebra, and the hypothesis `_hdeg` records $\operatorname{finrank}_{\mathbb Q}K=3$.
--
--   **The character $\mu$ and its non-inducedness.** A monoid homomorphism $\mu:(\mathbb A_K)^\times\to\mathbb C^\times$ is given, with `_hμ` asserting that $\mu$ is an admissible twist, i.e. trivial on the principal ideles coming from $K^\times$, continuous, and of absolute value $1$ at every idele. The hypothesis `_hns` asserts that there is *no* admissible twist $\eta$ of $\mathbb Q$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and whose contraction $p=\mathfrak P\cap\mathcal O_{\mathbb Q}$ is a prime at which $\eta$ is unramified one has $\mu(\mathrm{uniformizerIdele}\,K\,\mathfrak P)=\eta(\mathrm{uniformizerIdele}\,\mathbb Q\,p)^{f}$, $f$ the inertia degree `inertiaDeg'` of $\mathfrak P$ over $p$; here unramifiedness at $v$ means that the local component of the character is trivial on the units of the ring of integers of the completion at $v$.
--
--   **Archimedean components of $\mu$.** Functions $uR,aR$ are given on the real places of $K$ (values in $\mathbb C$, resp. $\mathbb Z/2$) and $uC,kC$ on the complex places (values in $\mathbb C$, resp. $\mathbb Z$). The hypotheses `huR`, `huC` say that `IsArchCompAt` holds, i.e. for every real place $w$ and every unit $x$ of the completion at $w$, the archimedean local character of $\mu$ at $w$ evaluated at $x$ is $\|x\|^{\operatorname{mult}(w)\,uR(w)}\,(\iota_w(x)/\|x\|)^{(aR(w)).\mathrm{val}}$, and likewise at every complex place $w$ with exponent $kC(w)$ in place of $(aR(w)).\mathrm{val}$.
--
--   **The character $\omega$ of $\mathbb Q$ (three clauses).** A monoid homomorphism $\omega:(\mathbb A_{\mathbb Q})^\times\to\mathbb C^\times$ is given together with `hω`, a conjunction of: (i) $\omega$ is an admissible twist of $\mathbb Q$ in the above sense; (ii) for every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ — `IsBadPlace` being the disjunction `IsRamifiedIn` $K$ at $p$ or `IsTwistRamifiedAbove` $K\,\mu$ at $p$ — the character $\omega$ is unramified at $p$ and $\operatorname{eulerCoeff}_{\mathbb Q}(\omega,p)$, namely $\omega(\mathrm{uniformizerIdele}\,\mathbb Q\,p)$, equals `inducedE3` $\mathbb Q$ applied to the coefficient system $\mathfrak P\mapsto\mu(\mathrm{uniformizerIdele}\,K\,\mathfrak P)$ at unramified $\mathfrak P$ (and $0$ at ramified $\mathfrak P$), that is minus the degree-$3$ coefficient of `inducedEulerPoly` at $p$; (iii) for *every* choice of archimedean data $uR,aR,uC,kC$ satisfying the conditions of `huR`, `huC`, and every real place $v$ of $\mathbb Q$, `IsArchCompAt` holds for $\omega$ at $v$ with complex parameter $\sum_w uR(w)+\sum_w 2\,uC(w)$ (finite sums over the real, resp. complex, places of $K$) and integer parameter $\sum_w (aR(w)).\mathrm{val}+\sum_w(kC(w)+1)$.
--
--   **Archimedean splitting, the base point $a$, the additive character, measures.** A homomorphism $E:(\mathbb A_{\mathbb Q,\infty})^\times\to(\mathbb A_{\mathbb Q})^\times$ is given with `hE`: the infinite part of $E(u)$ is $u$ and its finite part is $1$. A rational number $a$ is given with $a\neq0$ and $a=-1$, together with a unit $a_\infty$ of the infinite adele ring whose underlying element is the image of $a$, and an additive character $\psi_\infty$ on the infinite adele ring with $\psi_\infty(x)=\psi_{\mathrm{arch}}(a x)$ for the standard archimedean character `psiArch`. Borel measurable structures on the infinite adele ring and on its unit group are assumed; $\nu_{\mathrm{add}}$ is the measure equal to $|a|^{1/2}$ times the pushforward of Lebesgue measure along the inverse of `InfiniteAdeleRing.ringEquiv_mixedSpace ℚ`, and $\nu_{\mathrm{mul}}$ is a Haar measure on the unit group.
--
--   **The $\mathrm{GL}_2/\mathbb Q$ archimedean profile.** A parameter $P:\mathtt{RealArchParam}$ is given (either principal, with data $u_1,a_1,u_2,a_2$, or discrete, with data $u,k\ge1$), subject to `_hP₁`: if $P$ is principal with parameters $u_1,a_1,u_2,a_2$ then $|\operatorname{Re}(u_1-u_2)|<1$. Further data are a weight $kw:\mathbb Z/2\to(\text{infinite places of }\mathbb Q)\to\mathbb Z$, a radial profile $Wr:\mathbb Z/2\to(\text{places})\to\mathbb C\to\mathbb C$ and a function $WA:\mathbb Z/2\to\mathrm{GL}_2(\mathbb R)\to\mathbb C$, constrained by: `hkw1`, `hkw2` (the weight: $kw(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ in the principal case, $kw(\mathrm{par},w)=n+1$ in the discrete case of parameter $n$, where $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$); `hWr1` (in the principal case with equal signs $a_1=a_2$ and $\mathrm{par}=a_1$, the parity relation $Wr(\mathrm{par},w,-t)=(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w,t)$); `hWr2` (in the discrete case $Wr$ vanishes on $t<0$); `hWr3` and `hWr4` (Mellin identities: for the indicated parities $b$, for $\operatorname{Re}s$ large the Mellin transform of $t\mapsto (Wr(\mathrm{par},w,t)+(-1)^{b.\mathrm{val}}Wr(\mathrm{par},w,-t))/t$ converges and equals $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$, with the extra factor $(2s+u_1+u_2-1)/(4\pi)$ in the exceptional principal case $b=a_1+1$ of `hWr3`); and the $WA$-equivariance hypotheses `hWAN` (unipotent: $WA(\mathrm{par},u(x)h)=e^{-2\pi i a x}WA(\mathrm{par},h)$), `hWAZ` (central: scaling by $z\in\mathbb R^\times$ multiplies $WA$ by $|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}$), `hWAK` (right transformation under the subgroup `rowIsometrySubgroup₀ ℝ` by the weight character `archWeightCharℝ` of weight $kw(\mathrm{par},\mathrm{default})$), `hWAt` ($WA(\mathrm{par},\mathrm{diag}(t,1))=Wr(\mathrm{par},\mathrm{default},t)$ for $t\in\mathbb R^\times$) and `hWAc` (continuity of each $WA(\mathrm{par},\cdot)$). Also given is $w_{0R}\in\mathrm{GL}_2(\mathbb R)$ with underlying matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and a parity $\mathrm{par}_0\in\mathbb Z/2$.
--
--   **The distinguished real place and the $\mathrm{GL}_2$ datum at the remaining places.** A real place $w_0$ of $K$ is given, and a parameter $P_2$ subject to `hP₂`: either $K$ has exactly three real places $w_0,w_1,w_2$ (pairwise distinct, exhausting the infinite places) and $P_2$ is principal with data $(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$; or $K$ has a complex place $w_C$ with the infinite places exhausted by $w_C,w_0$, and then either $kC(w_C)\neq0$ and $P_2$ is discrete with data $(uC(w_C),|kC(w_C)|)$, or $kC(w_C)=0$ and $P_2$ is principal with data $(uC(w_C),0,uC(w_C),1)$. An archimedean Whittaker datum $D:\mathtt{ArchDatumR}\,P_2$ is given, whose component $D.W:M_2(\mathbb R)\to\mathbb C$ is smooth on the invertible locus and satisfies the unipotent and central transformation laws together with the Tate-type zeta axioms of the structure, and an integer $k_0$, subject to: `hDW` ($D.W(xr)=\mathtt{archWeightChar\mathbb R}\,k_0(r)\,D.W(x)$ for $r$ in `rowIsometrySubgroup₀ ℝ`); `hDE` (`IsCasimirEigen`: $\mathtt{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for $\det x\neq0$); `hDnz` ($D.W$ does not vanish identically on $\mathrm{GL}_2(\mathbb R)$); `hk₀min` ($k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2\bmod 2$ in the principal case, $k_0=m+1$ in the discrete case of parameter $m$). Finally `hPw1` requires $P$ to be principal with $a_1\neq a_2$ (the weight-one condition), `hk₀` requires $k_0=0$, and `hodd` requires $aR(w_0)\neq a_1$ whenever $P_2$ is principal with first sign $a_1$.
--
--   **The minor section.** A function $S:M_{2\times3}(\mathbb R)\to\mathbb C$ is given with $hS$: $S(M)=\bigl((M_{00}-iM_{01})M_{12}-(M_{10}-iM_{11})M_{02}\bigr)\cdot\mathtt{gaussian3}(M)$, where $\mathtt{gaussian3}(M)=\exp\bigl(-\pi\sum_{i,b}M_{ib}^2\bigr)$. A complex number $s$ is given.
--
--   **Conclusion.** The following two iterated integrals, over $a_2$ in $(0,\infty)$ and $a_1$ in $\mathbb R$ (Lebesgue measure in both variables), agree.
--
--   On the left, the integrand vanishes unless $a_1\neq0$ and $a_2>0$; in that case, with $q:=\mathtt{upperUnit}\,a_1\,0\,a_2=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}\in\mathrm{GL}_2(\mathbb R)$, it is
--   $$\bigl(|\det q|\cdot WA(\mathrm{par}_0,\;w_{0R}\cdot{}^t q^{-1})\bigr)\cdot \mathtt{dualWhittakerFn3}\bigl(\mathtt{jacquetVector3}\,D\,(uR\,w_0)\,(aR\,w_0)\,a\,\psi_\infty\,S\bigr)(\hat q)\cdot|\det q|^{\,s-1/2}\cdot a_1^{-2},$$
--   where ${}^tq^{-1}$ is [`RSCarrier.transposeInv`](def/LanglandsTunnell_RSCarrier.html#L31), $\hat q$ is the image of $q$ under the inclusion of $\mathrm{GL}_2(\mathbb R)$ at the real place of $\mathbb Q$ into the adelic $\mathrm{GL}_2$, followed by the upper-left block embedding `iota` into the adelic $\mathrm{GL}_3$ and by passage to the archimedean component, and `dualWhittakerFn3` $W$ evaluated at $g$ means $W(\mathtt{longWeyl3}\cdot\mathtt{transposeInv3}\,g)$ with $\mathtt{longWeyl3}$ the permutation matrix $\begin{pmatrix}0&0&1\\0&1&0\\1&0&0\end{pmatrix}$.
--
--   On the right, the integrand again vanishes unless $a_1\neq0$ and $a_2>0$, in which case it is the product of:
--   $|a_1a_2|$;
--   $$i^{\,kw(\mathrm{par}_0,\mathrm{default})}\cdot\Bigl(|-a_1^{-1}|^{\,P.\mathrm{centralExponent}+1}\bigl((-a_1^{-1})/|-a_1^{-1}|\bigr)^{P.\mathrm{centralSign}.\mathrm{val}}\Bigr)\cdot Wr(\mathrm{par}_0,\mathrm{default},-a_1/a_2);$$
--   the factor
--   $$\chi_{uR(w_0)+1,\,aR(w_0)}\bigl(-(a_1a_2)^{-1}\bigr)\cdot\int_{e\in M_2(\mathbb R)}\Bigl[\,e^{-\pi\left(a_2^{-2}(e_{01}^2+e_{11}^2)+(e_{00}^2+e_{10}^2)\right)}\cdot\frac{a_1^2}{|\det e|}\cdot\Bigl(-i\,a\,a_1\bigl(\rho_0 e_{10}-\rho_1 e_{00}\bigr)+i\,a_2^{-1}\det e\Bigr)\cdot e^{-\pi a^2a_1^2(\rho_0^2+\rho_1^2)}\Bigr]\cdot\chi_{uR(w_0)+2,\,aR(w_0)}(\det e)\,|\det e|^{-2}\cdot D.W\bigl(\mathrm{diag}(a,1)\,e^{-1}\bigr)\,de,$$
--   where $\rho_0=(e^{-1})_{10}$, $\rho_1=(e^{-1})_{11}$, $\chi_{u,\epsilon}(y)=|y|^{u}$ if $\epsilon=0$ and $|y|^{u}\operatorname{sgn}(y)$ if $\epsilon=1$ (the function `ArchR.quasiChar`), and $\mathrm{diag}(a,1)$ is `ArchR.diagOne` at $a$;
--   and finally $|a_1a_2|^{\,s-1/2}$ and $a_1^{-2}$.
--
--   The identity is asserted for the given $s$ with no convergence hypothesis beyond those listed: both sides are the iterated integrals as written.
--
--   This is the dual-side frame unfolding in the archimedean Rankin–Selberg analysis of the cubic induction: the dual torus pair attached to the minor Schwartz section is rewritten as one explicit $(a_1,a_2,e)$-integral, by combining the reflection formula for the $\mathrm{GL}_2$ archimedean profile $WA$ at $w_{0R}\,{}^tq^{-1}$, the evaluation of the Jacquet vector at $\mathtt{longWeyl3}\cdot\mathtt{transposeInv3}$ of the embedded Siegel element, and the closed form of the dual Godement configuration integral for the minor section. It feeds the computation of the archimedean root number and gamma factor of the dual torus pair in [`LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile`](thm.html#LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_minorSection_gaussian3.lean

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

theorem LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_minorSection_gaussian3
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
    (hk₀ : k₀ = 0)
    (hodd : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ → aR w₀ h₀ ≠ a₁)
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 0 1 : ℝ) : ℂ)) * ((M 1 2 : ℝ) : ℂ) -
        (((M 1 0 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ)) * ((M 0 2 : ℝ) : ℂ)) * gaussian3 M)
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
                      ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
                    (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
                    (-Complex.I * (a : ℂ) * (a₁ : ℂ) *
                        ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) * ((e 1 0 : ℝ) : ℂ) - (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ) * ((e 0 0 : ℝ) : ℂ)) +
                      Complex.I * (a₂⁻¹ : ℂ) * (((Matrix.of e).det : ℝ) : ℂ)) *
                    (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
                        (ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) *
                        D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹)) *
                  (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0) := by sorry
