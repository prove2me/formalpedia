-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_minorSection_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_minorSection_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/aed5a10f-f9fb-5186-a549-e13e924455c1
-- title:
--   Weight-one minor-section torus-pair identities with archimedean Γ-factors
-- statement:
--   Global data. $K$ is a number field with $[K:\mathbb{Q}]=3$ (`_hdeg`), equipped with an integral algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$. The character $\mu\colon (\mathbb{A}_K)^\times\to\mathbb{C}^\times$ is an admissible twist (`_hμ`): it is trivial on $K^\times$, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` asserts that $\mu$ admits no descent to $\mathbb{Q}$ in the following sense: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose trace $p=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ is unramified for $\eta$, the value of $\mu$ on the uniformiser idele at $\mathfrak{P}$ equals the value of $\eta$ on the uniformiser idele at $p$ raised to the inertia degree of $\mathfrak{P}$ over $p$. The functions $uR,aR$ (on the real places of $K$, with values in $\mathbb{C}$ and $\mathbb{Z}/2$) and $uC,kC$ (on the complex places, with values in $\mathbb{C}$ and $\mathbb{Z}$) record the archimedean components of $\mu$: `huR` and `huC` state that at each real place $w$ the local character of $\mu$ is $x\mapsto \lVert x\rVert^{\mathrm{mult}(w)\,uR(w)}\,(x/\lVert x\rVert)^{(aR\,w).\mathrm{val}}$ and at each complex place $x\mapsto \lVert x\rVert^{\mathrm{mult}(w)\,uC(w)}\,(x/\lVert x\rVert)^{kC(w)}$.
--
--   The character $\omega\colon(\mathbb{A}_{\mathbb{Q}})^\times\to\mathbb{C}^\times$ satisfies the three clauses of `hω`: it is an admissible twist of $\mathbb{Q}$; at every rational prime $p$ which is not a bad place for $(K,\mu)$ (that is, neither ramified in $K$ nor twist-ramified above), $\omega$ is unramified and its Euler coefficient $\omega(\text{uniformiser idele at }p)$ equals $\mathrm{inducedE}3$ of the coefficient system $\mathfrak{P}\mapsto\mu(\text{uniformiser idele at }\mathfrak{P})$ (the negative of the degree-$3$ coefficient of the induced Euler polynomial); and, for every quadruple $(uR,aR,uC,kC)$ of archimedean exponents compatible with $\mu$ as above, the archimedean component of $\omega$ at the real place of $\mathbb{Q}$ is given by the exponent $\sum_{w\text{ real}}uR(w)+\sum_{w\text{ complex}}2\,uC(w)$ and the integer $\sum_{w\text{ real}}(aR\,w).\mathrm{val}+\sum_{w\text{ complex}}(kC(w)+1)$ (finsums over the infinite places of $K$).
--
--   Normalisation data. $E$ is a monoid homomorphism from the infinite ideles of $\mathbb{Q}$ to the full ideles splitting the infinite part, in that `hE` requires the infinite part of $E(u)$ to be $u$ and its finite part to be $1$. The rational number $a$ is non-zero (`ha`) and equal to $-1$ (`ha1`), $aInf$ is an infinite idele whose underlying element is the image of $a$ (`haInf`), and $\psi_\infty$ is the additive character $x\mapsto\psi^{\mathrm{arch}}(a x)$ of the infinite adeles (`hpsiInf`). Measurable and Borel structures on the infinite adeles and on their units are fixed; $\nu_{\mathrm{add}}$ is the Lebesgue measure of the mixed space transported to the infinite adeles and scaled by $\lvert a\rvert^{1/2}$ (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the infinite ideles.
--
--   The $\mathrm{GL}_2$ archimedean package. $P$ is a real archimedean parameter subject to `_hP₁`: if $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $\lvert\mathrm{Re}(u_1-u_2)\rvert<1$. The data $kw$ (weights), $Wr$ (torus functions on $\mathbb{R}$) and $WA$ (functions on $\mathrm{GL}_2(\mathbb{R})$), each indexed by a parity in $\mathbb{Z}/2$, satisfy: `hkw1`, in the principal case $kw(\mathrm{par})=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$, and `hkw2`, in the discrete case $P=\mathrm{discrete}(u_0,n)$ one has $kw(\mathrm{par})=n+1$; `hWr1`, for $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$ the function $Wr$ satisfies $Wr(-t)=(-1)^{a_1.\mathrm{val}}Wr(t)$; `hWr2`, for $P$ discrete $Wr$ vanishes on the negative half-line; `hWr3`, for $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$ there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr(t)+(-1)^{a_1.\mathrm{val}}Wr(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}(0,a_1)$; `hWr4`, for every $b$ equal to $\mathrm{par}$ or to $\mathrm{par}+P.\mathrm{centralSign}$ there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr(t)+(-1)^{b.\mathrm{val}}Wr(-t))/t$ converges and equals the archimedean factor of $P.\mathrm{twist}(0,b)$ at $s$. For $WA$: `hWAN` gives $WA(\mathrm{par})(u(x)h)=e^{-2\pi i a x}\,WA(\mathrm{par})(h)$ for unipotent $u(x)=\binom{1\ x}{0\ 1}$; `hWAZ` gives the central law $WA(\mathrm{par})(z\cdot h)=\lvert z\rvert^{P.\mathrm{centralExponent}+1}(z/\lvert z\rvert)^{(P.\mathrm{centralSign}).\mathrm{val}}WA(\mathrm{par})(h)$; `hWAK` gives right equivariance $WA(\mathrm{par})(h\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(kw(\mathrm{par}))(\kappa)\,WA(\mathrm{par})(h)$ for $\kappa$ in the row-isometry subgroup; `hWAt` identifies $WA(\mathrm{par})(\mathrm{diag}(t,1))$ with $Wr(\mathrm{par})(t)$; `hWAc` asserts continuity of each $WA(\mathrm{par})$. Finally $w_{0R}\in\mathrm{GL}_2(\mathbb{R})$ is the matrix $\binom{0\ 1}{1\ 0}$ (`hw₀R`).
--
--   The Levi datum. $w_0$ is a real place of $K$, and $P_2$ is a real archimedean parameter tied to the signature of $K$ by `hP₂`: either $K$ has exactly three real places $w_0,w_1,w_2$ and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$, or $K$ has exactly one complex place $w_C$ besides $w_0$ and $P_2=\mathrm{discrete}(uC(w_C),\lvert kC(w_C)\rvert)$ when $kC(w_C)\neq 0$, respectively $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$ when $kC(w_C)=0$. $D$ is a real archimedean Whittaker datum for $P_2$ (a smooth function $D.W$ on $2\times 2$ real matrices with the unipotent and central transformation laws, an entire completed zeta function with its integral representation, functional equation, finite order and decay bounds) and $k_0\in\mathbb{Z}$ a weight, with `hDW` stating right equivariance $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in the row-isometry subgroup, `hDE` stating that $D$ is a Casimir eigenfunction with eigenvalue $P_2.\mathrm{laplaceEigenvalue}$ on invertible matrices, `hDnz` that $D.W$ is not identically zero, and `hk₀min` that $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \pmod 2$ in the principal case and $k_0=m+1$ in the discrete case $P_2=\mathrm{discrete}(u,m)$.
--
--   Branch hypotheses and section. `hPw1` places $P$ in the weight-one principal case: $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $a_1\neq a_2$; `hk₀` fixes $k_0=0$; `hodd` requires, whenever $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$, that $aR(w_0)\neq a_1$. (Under `hPw1` the antecedents of `hkw2`, `hWr1`, `hWr2` and `hWr3`, which demand that $P$ be discrete or have equal parities, cannot be met, so these clauses carry no content in this branch.) The parity $\mathrm{par}_0\in\mathbb{Z}/2$ is arbitrary, and $S$ is the minor section on $2\times 3$ real matrices, $$S(M)=\bigl[(M_{00}-iM_{01})M_{12}-(M_{10}-iM_{11})M_{02}\bigr]\exp\Bigl(-\pi\sum_{i<2,\,b<3}M_{ib}^{2}\Bigr),$$ as prescribed by `hS`.
--
--   Conclusion. There exist an abscissa $\sigma_a\in\mathbb{R}$ and a constant $e\in\mathbb{C}$, $e\neq 0$, such that the following two identities hold, with the same $e$ in both.
--
--   First, for every $s$ with $\mathrm{Re}\,s>\sigma_a$, the integral over $2\times 2$ real matrices $g$ of $$\mathrm{quasiChar}\bigl(uR(w_0)+2,\;aR(w_0)\bigr)(\det g)\cdot\lvert\det g\rvert^{-2}\cdot\Bigl(\int_{\mathbb{R}}Wr(\mathrm{par}_0)(t)\,D.W\bigl(\mathrm{diag}(a t,1)\,g^{-1}\bigr)\lvert t\rvert^{\,s-1/2}\,t^{-2}\,dt\Bigr)\cdot\Bigl(\int_{0}^{\infty}y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,\mathrm{godementInner3}\bigl(\psi_\infty\ast y,\,S,\,g,\,1\bigr)\,dy\Bigr)$$ equals $e$ times the product of $\Gamma_{\mathbb{R}}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGammaR}$ of $K$ for the constant parameter $P$ twisted by $(uR,aR)$ (the sum over the real places $w$ of the $\Gamma_{\mathbb{R}}$-shift multiset of $P.\mathrm{twist}(uR(w),aR(w))$), times the product of $\Gamma_{\mathbb{C}}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGammaC}$ for the constant parameters $P$ at the real places and $P.\mathrm{baseChange}$ at the complex places, twisted by $(uR,aR)$ and $(uC,kC)$ respectively. Here $\mathrm{quasiChar}(u,\alpha)(y)=\lvert y\rvert^{u}$ if $\alpha=0$ and $\lvert y\rvert^{u}\mathrm{sign}(y)$ otherwise, $\mathrm{diag}(\tau,1)$ denotes $\binom{\tau\ 0}{0\ 1}$, and $\mathrm{godementInner3}$ is the integral over $v\in\mathbb{R}^2$ of $S$ evaluated at $g$ times the $2\times 3$ matrix whose rows are the first two rows of the identity shifted by $v_0$, $v_1$ times its third row, against the character $\psi_\infty$ shifted by $y$ and evaluated at $-v_1$.
--
--   Second, for every $s$ with $\mathrm{Re}\,s>\sigma_a$, the iterated integral over $a_2\in(0,\infty)$ and $a_1\in\mathbb{R}$ of the integrand which, on the locus $a_1\neq 0$ and $a_2>0$, is $$\lvert\det q\rvert\;WA(\mathrm{par}_0)\bigl(w_{0R}\cdot{}^{t}q^{-1}\bigr)\cdot\mathrm{dualWhittakerFn3}\bigl(\mathrm{jacquetVector3}(D,uR(w_0),aR(w_0),a,\psi_\infty,S)\bigr)\bigl(\text{arch. component of the }\mathrm{GL}_3\text{-image of }q\bigr)\cdot\lvert\det q\rvert^{\,s-1/2}\cdot a_1^{-2}$$ and $0$ elsewhere, where $q=\binom{a_1\ 0}{0\ a_2}$ and the $\mathrm{GL}_3$-argument is obtained by embedding $q$ into the adelic $\mathrm{GL}_2$ of $\mathbb{Q}$ at the real place, then into adelic $\mathrm{GL}_3$ by $\iota$, and taking the archimedean component, equals $$\Bigl(\mathrm{archRootNumber}\,(K,P,P.\mathrm{baseChange},uR,aR,uC,kC)\cdot(-1)^{(P.\mathrm{centralSign}).\mathrm{val}}\cdot(-1)^{\#\{\text{complex places of }K\}}\cdot e\Bigr)$$ times the product of $\Gamma_{\mathbb{R}}(s+\tfrac12+x)$ over $\mathrm{twistedGammaR}$ for the dual parameter $P.\mathrm{dual}$ twisted by $(-uR,aR)$, times the product of $\Gamma_{\mathbb{C}}(s+\tfrac12+x)$ over $\mathrm{twistedGammaC}$ for the dual parameters $P.\mathrm{dual}$ at the real places and $(P.\mathrm{baseChange}).\mathrm{dual}$ at the complex places, twisted by $(-uR,aR)$ and $(-uC,-kC)$. The root number is the product over the real places of the $\varepsilon$-factors of $P.\mathrm{twist}(uR(w),aR(w))$ times the product over the complex places of the $\varepsilon$-factors of $(P.\mathrm{baseChange}).\mathrm{twist}(uC(w),kC(w))$; $\mathrm{dualWhittakerFn3}$ sends a function $W$ on $\mathrm{GL}_3$ to $g\mapsto W(w_3\cdot{}^{t}g^{-1})$ with $w_3$ the long Weyl element, and $\mathrm{jacquetVector3}$ is $\mathrm{quasiChar}(uR(w_0)+1,aR(w_0))(\det g_\infty)$ times the integral over $2\times2$ real matrices of the Jacquet integrand built from $D$, $a$, $\psi_\infty$ and $S$.
--
--   This is the archimedean input for the $\mathrm{GL}_3\times\mathrm{GL}_2$ Rankin–Selberg unfolding in the cubic-induction (Langlands–Tunnell) converse-theorem argument: in the weight-one principal branch, with minimal Levi weight $k_0=0$ and opposite parity at $w_0$, the unfolded torus-pair integral attached to the minor Schwartz section and its dual counterpart are evaluated as one and the same non-zero constant times the archimedean $\Gamma$-factors of the parameter and of its dual, the dual side acquiring the archimedean root number together with two sign factors. It is cited by [`LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen), where it supplies the branch in which the Levi weight vanishes, and it rests on the explicit minor-section evaluations and on the construction of the archimedean Whittaker datum $D$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_minorSection_gaussian3.lean

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

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell
open LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_minorSection_gaussian3
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
        (((M 1 0 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ)) * ((M 0 2 : ℝ) : ℂ)) * gaussian3 M) :
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
