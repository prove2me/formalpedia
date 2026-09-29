-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/f3dbbb23-f931-560d-8a05-dd5536e14994
-- title:
--   Dual minor-section archimedean torus pair equals ε_∞ times Γ-factors
-- statement:
--   Throughout, $K$ is a number field of degree $3$ over $\mathbb{Q}$, equipped with an integral algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$, and $\mu\colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ is an admissible twist, i.e. a continuous unitary character trivial on the principal ideles (`IsAdmissibleTwist`). The hypothesis `_hns` is the non-descent condition: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that, for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and over a prime of $\mathcal{O}_{\mathbb{Q}}$ at which $\eta$ is unramified, the value $\mu$ takes on a uniformiser idele at $\mathfrak{P}$ equals the corresponding value of $\eta$ raised to the inertia degree of $\mathfrak{P}$.
--
--   The archimedean parameters of $\mu$ are encoded by $uR, aR$ on the real places and $uC, kC$ on the complex places of $K$: the clauses `huR` and `huC` say that at each real place $w$ the local component of $\mu$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,uR(w)}(x/\|x\|)^{aR(w)}$ (with the exponent the natural representative of $aR(w)\in\mathbb{Z}/2$), and similarly at each complex place with exponents $uC(w)$, $kC(w)$.
--
--   The character $\omega$ of $(\mathbb{A}_{\mathbb{Q}})^\times$ satisfies `hω`, three clauses: $\omega$ is an admissible twist; at every prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ which is not a bad place for $(K,\mu)$ (neither ramified in $K$ nor twist-ramified above) $\omega$ is unramified and its Euler coefficient equals $-$ the degree-$3$ coefficient of the induced Euler polynomial built from the unramified coefficients of $\mu$ (`inducedE3 ℚ (inducedCoeff K μ) p`); and, for any archimedean exponent data for $\mu$ as above, at each real place $v$ of $\mathbb{Q}$ the archimedean component of $\omega$ has exponents $\big(\sum_{w\ \mathrm{real}} uR(w) + \sum_{w\ \mathrm{complex}} 2\,uC(w)\big)$ and $\big(\sum_{w\ \mathrm{real}} aR(w) + \sum_{w\ \mathrm{complex}} (kC(w)+1)\big)$, the sums being finite sums over the infinite places.
--
--   The adelic frame consists of: a splitting $E$ of the infinite idele units into the full idele units, with `hE` asserting that the infinite part of $E(u)$ is $u$ and its finite part is $1$; a rational number $a$ with $a\neq 0$ and $a=-1$; an infinite idele unit $aInf$ whose underlying element is the image of $a$; an additive character $\psi_\infty$ of the infinite adele ring given by $x\mapsto \psi_{\mathrm{arch}}(a x)$ for the standard archimedean character; measurable and Borel structures on the infinite adele ring and on its unit group; an additive measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the transport of Lebesgue measure along the inverse of the identification of the infinite adele ring with the mixed space; and a Haar measure $\nu_{\mathrm{mul}}$ on the infinite idele units.
--
--   The archimedean Whittaker frame is a real archimedean parameter $P$ with the separation condition `_hP₁` (if $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $|\operatorname{Re}(u_1-u_2)|<1$), a weight function $kw$, radial functions $Wr$ and a function $WA$ on $\mathrm{GL}_2(\mathbb{R})$, all indexed by a parity $\mathrm{par}\in\mathbb{Z}/2$. Their defining properties are: `hkw1`, in the principal case $kw(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$; `hkw2`, in the discrete case $kw(\mathrm{par},w)=n+1$; `hWr1`, in the principal case with equal signs $a_1=a_2$ and $\mathrm{par}=a_1$, the reflection law $Wr(\mathrm{par},w,-t)=(-1)^{a_1}Wr(\mathrm{par},w,t)$; `hWr2`, in the discrete case $Wr$ vanishes on the negative half-line; `hWr3`, in the principal case with equal signs and $\mathrm{par}=a_1+1$, there is an abscissa beyond which the Mellin transform of $t\mapsto (Wr(\mathrm{par},w,t)+(-1)^{a_1}Wr(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$; `hWr4`, for every $b$ equal to $\mathrm{par}$ or to $\mathrm{par}+\sigma(P)$, where $\sigma(P)$ is the central sign, the analogous Mellin transform converges and equals the archimedean factor of $P$ twisted by $(0,b)$; `hWAN`, $WA(\mathrm{par},n(x)h)=e^{-2\pi i a x}WA(\mathrm{par},h)$ for the unipotent $n(x)$; `hWAZ`, $WA(\mathrm{par},z\cdot h)=|z|^{\,c(P)+1}(z/|z|)^{\sigma(P)}WA(\mathrm{par},h)$ for scalar $z$, with $c(P)$ the central exponent; `hWAK`, right equivariance of $WA$ under `rowIsometrySubgroup₀ ℝ` through the weight character `archWeightCharℝ (kw par default)`; `hWAt`, $WA(\mathrm{par},\mathrm{diag}(t,1))=Wr(\mathrm{par},\text{default},t)$; and `hWAc`, continuity of each $WA(\mathrm{par},\cdot)$. Finally $w_{0R}\in\mathrm{GL}_2(\mathbb{R})$ is the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   The cubic archimedean profile consists of a real place $w_0$ of $K$ and a second real parameter $P_2$, subject to `hP₂`: either $K$ has exactly the three real places $w_0,w_1,w_2$ (pairwise distinct and exhausting the infinite places) and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$, or $K$ has exactly one complex place $w_C$ besides $w_0$ and either $kC(w_C)\neq 0$ with $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$, or $kC(w_C)=0$ with $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$.
--
--   The archimedean datum is $D$, an `ArchDatumR P₂`, together with an integer $k_0$ such that: `hDW`, $D.W$ is right-equivariant under `rowIsometrySubgroup₀ ℝ` through `archWeightCharℝ k₀`; `hDE`, $D.W$ is an eigenfunction of the matrix Casimir operator with eigenvalue the Laplace eigenvalue of $P_2$ on invertible matrices; `hDnz`, $D.W$ does not vanish identically; and `hk₀min`, the minimality of the weight: in the principal case $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, and in the discrete case $k_0=m+1$. Further, `hPw1` requires $P$ to be principal with unequal signs $a_1\neq a_2$; `hk₀` requires $k_0=0$; `hodd` requires, in the principal case for $P_2$, that $aR(w_0)$ differs from the first sign of $P_2$. A parity $\mathrm{par}_0\in\mathbb{Z}/2$ is fixed, and the minor section is the Schwartz-type function
--   $$S(M)=\big((M_{00}-iM_{01})M_{12}-(M_{10}-iM_{11})M_{02}\big)\cdot g_3(M)$$
--   on $2\times 3$ real matrices, where $g_3(M)=\exp(-\pi\sum_{i,b}M_{ib}^2)$ is the Gaussian.
--
--   Finally, the torus profile of the datum is specified: $u_1,u_2\in\mathbb{C}$ and $c\in\mathbb{Z}/2$ with $P_2=\mathrm{principal}(u_1,c,u_2,c)$ (both signs equal to $c$), and $\rho\in\mathbb{C}$ such that for every $\tau>0$
--   $$D.W\big(\mathrm{diag}(\tau,1)\big)=\rho\,\tau\cdot\Big(4\int_0^\infty r^{u_1}e^{-\pi r^2}\,(\tau/r)^{u_2}e^{-\pi(\tau/r)^2}\,\frac{dr}{r}\Big).$$
--
--   Under these hypotheses there exists $\sigma_a\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\operatorname{Re} s>\sigma_a$ the iterated integral
--   $$\int_{a_2>0}\int_{a_1\in\mathbb{R}} \Big(|\det q|\; WA(\mathrm{par}_0, w_{0R}\cdot{}^{t}q^{-1})\; \cdot \big(\text{dual Whittaker value}\big)\Big)\,|\det q|^{\,s-1/2}\,a_1^{-2}$$
--   equals the stated right-hand side. Here the integrand is defined to be $0$ unless $a_1\neq 0$ and $a_2>0$, in which case $q=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$ is the upper-triangular element [`AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂`](def/AutomorphicForm_SiegelCoordinates.html#L126), ${}^tq^{-1}$ is [`RSCarrier.transposeInv q`](def/LanglandsTunnell_RSCarrier.html#L31), and the dual Whittaker value is `dualWhittakerFn3` applied to the Jacquet vector $J=$ `jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) a psiInf S`, evaluated at the archimedean $\mathrm{GL}_3$-component of the image of $q$ under the embedding of $\mathrm{GL}_2(\mathbb{R})$ at the real place of $\mathbb{Q}$ followed by `iota` into the adelic $\mathrm{GL}_3$; by definition `dualWhittakerFn3 J g = J(w_3\cdot {}^tg^{-1})` for the long Weyl element $w_3$ of $\mathrm{GL}_3$, and $J(g)$ is the product of the quasicharacter value $\mathrm{quasiChar}(uR(w_0)+1, aR(w_0))$ at $\det$ of the real matrix of $g$ with the integral over $2\times 2$ real matrices $e$ of the Jacquet integrand `jacquetIntegrand3 D (uR w₀ h₀) (aR w₀ h₀) a psiInf S g e`.
--
--   The value of the integral is
--   $$\Big(\varepsilon_\infty\cdot(-1)^{\sigma(P)}\cdot(-1)^{r_2}\Big)\cdot\Big(\pi\, i\,(-1)^{c}\,\rho\Big)\cdot\prod_{x}\Gamma_{\mathbb{R}}\!\big(s+\tfrac12+x\big)\cdot\prod_{y}\Gamma_{\mathbb{C}}\!\big(s+\tfrac12+y\big),$$
--   where $\varepsilon_\infty=$ `archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC` is the product over the real places of $K$ of the epsilon factor of $P$ twisted by $(uR(w),aR(w))$ times the product over the complex places of the epsilon factor of the base change of $P$ twisted by $(uC(w),kC(w))$; $\sigma(P)$ is the central sign of $P$ and $r_2$ is the number of complex places of $K$; the exponents $x$ run over the multiset `twistedGammaR K` formed from the duals of the real parameters with twists $(-uR(w),aR(w))$, and the exponents $y$ over the multiset `twistedGammaC K` formed from the duals of the real and complex parameters with twists $(-uR(w),aR(w))$ and $(-uC(w),-kC(w))$ respectively.
--
--   This is the dual half of the archimedean torus-pair computation for the minor section of the cubic Rankin–Selberg construction: it evaluates the unfolded dual archimedean integral, taken against $WA$ at the Weyl-translated inverse transpose and the dual Whittaker function of the Jacquet vector of the Gaussian minor section, as the archimedean root number together with the explicit constant $\pi i(-1)^c\rho$ times the dual product of $\Gamma_{\mathbb{R}}$- and $\Gamma_{\mathbb{C}}$-factors. It is the companion of the primal evaluation in the same frame and is used by [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_minorSection_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_minorSection_gaussian3), which combines the two halves into the functional equation of the archimedean Rankin–Selberg factor needed for the converse theorem input to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile
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

    (u₁ u₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c u₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((τ) / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * ((τ) / r) ^ 2)) : ℂ)) / (r : ℂ))) :
    ∃ σa : ℝ, ∀ s : ℂ, σa < s.re →
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = ((archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) * (((Real.pi : ℂ) * Complex.I * (-1 : ℂ) ^ c.val) * ρ)) * (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
                    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod) := by sorry
