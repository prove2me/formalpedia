-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/4102c018-868e-52b2-9b75-9d96dacf6253
-- title:
--   Explicit dual archimedean torus pair: root number times π(-1)ᶜρ times Γ-factor
-- statement:
--   The setting is the following. $K$ is a number field whose ring of integers is an integral algebra over $\mathcal O_{\mathbb Q}$, and the hypothesis `_hdeg` asserts $[K:\mathbb Q]=3$.
--
--   *Character data.* $\mu\colon (\mathbb A_K)^\times\to\mathbb C^\times$ is a homomorphism which is admissible (`_hμ`), i.e. trivial on the image of $K^\times$, continuous, and of absolute value $1$ at every idele. The hypothesis `_hns` asserts that no admissible character $\eta$ of $(\mathbb A_{\mathbb Q})^\times$ satisfies: for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and such that $\eta$ is unramified at the prime $p$ of $\mathcal O_{\mathbb Q}$ below $\mathfrak P$, one has $\mu(\varpi_{\mathfrak P})=\eta(\varpi_p)^{f}$, with $f$ the inertia degree of $\mathfrak P$ over $p$ and $\varpi$ the idele `uniformizerIdele` supported at the given prime; here 'unramified at $v$' means that the local character kills every unit of the completion at $v$ whose underlying element and inverse are both integral.
--
--   *Archimedean components of $\mu$.* The data $uR,aR$ assign to each real place $w$ of $K$ a complex number $uR(w)$ and a class $aR(w)\in\mathbb Z/2$, and $uC,kC$ assign to each complex place $w$ a complex number $uC(w)$ and an integer $kC(w)$. The hypotheses `huR`, `huC` state that the archimedean local component of $\mu$ at $w$ is $x\mapsto \|x\|^{\,\mathrm{mult}(w)\,u}\bigl(\iota_w(x)/\|x\|\bigr)^{a}$, with $(u,a)=(uR(w),(aR(w)).\mathrm{val})$ at real places and $(u,a)=(uC(w),kC(w))$ at complex places.
--
--   *The character $\omega$ of $\mathbb Q$.* $\omega\colon(\mathbb A_{\mathbb Q})^\times\to\mathbb C^\times$ satisfies the three clauses of `hω`: $\omega$ is admissible; at every prime $p$ of $\mathcal O_{\mathbb Q}$ that is not bad for $(K,\mu)$ — i.e. $p$ is neither ramified in $K$ nor twist-ramified above for $\mu$ — $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals $\mathrm{inducedE3}$ of the unramified Satake data $\mathrm{inducedCoeff}\,K\,\mu$ at $p$, namely minus the degree-$3$ coefficient of the induced Euler polynomial; and, for every quadruple $(uR,aR,uC,kC)$ satisfying the archimedean-component conditions above, the archimedean component of $\omega$ at the real place $v$ of $\mathbb Q$ has exponent $\bigl(\sum_{w\ \mathrm{real}} uR(w)\bigr)+\bigl(\sum_{w\ \mathrm{complex}}2\,uC(w)\bigr)$ and integer parameter $\bigl(\sum_{w\ \mathrm{real}}(aR(w)).\mathrm{val}\bigr)+\bigl(\sum_{w\ \mathrm{complex}}(kC(w)+1)\bigr)$ (finite sums).
--
--   *Splitting, additive character, measures.* $E$ is a homomorphism $(\mathbb A_{\mathbb Q,\infty})^\times\to(\mathbb A_{\mathbb Q})^\times$ with, by `hE`, infinite part the identity and finite part $1$. The rational number $a$ is nonzero and equal to $-1$ (`ha`, `ha1`); $aInf$ is a unit of the infinite adele ring whose underlying element is the image of $a$ (`haInf`); $\psi_\infty$ is the additive character $x\mapsto \psi_{\mathrm{arch}}(a\,x)$ (`hpsiInf`). The infinite adele ring and its unit group carry measurable and Borel structures; $\nu_{\mathrm{add}}$ is, by `hν_add`, $|a|^{1/2}$ times the pushforward of Lebesgue measure on the mixed space under the inverse of the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace`, and $\nu_{\mathrm{mul}}$ is a Haar measure on the unit group.
--
--   *The weight-one parameter $P$ and the $\mathrm{GL}_2(\mathbb R)$ Whittaker data.* $P$ is a real archimedean parameter, of principal or discrete type. By `_hP₁`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $|\mathrm{Re}(u_1-u_2)|<1$; by `hPw1`, $P$ is indeed of principal type, with $a_1\neq a_2$ (weight one). The data are: integers $kw(\mathrm{par},w)$, functions $Wr(\mathrm{par},w)\colon\mathbb R\to\mathbb C$ and $WA(\mathrm{par})\colon\mathrm{GL}_2(\mathbb R)\to\mathbb C$ indexed by $\mathrm{par}\in\mathbb Z/2$ and by the infinite places of $\mathbb Q$. Their hypotheses are: `hkw1`, in the principal case $kw(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$, and `hkw2`, in the discrete case $P=\mathrm{discrete}(u_0,n)$ with $n\ge1$ one has $kw(\mathrm{par},w)=n+1$; `hWr1`, in the principal case with equal signs $a_1=a_2$ and $\mathrm{par}=a_1$, $Wr(\mathrm{par},w)(-t)=(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(t)$; `hWr2`, in the discrete case $Wr(\mathrm{par},w)$ vanishes on the negative axis; `hWr3`, in the principal case with equal signs and $\mathrm{par}=a_1+1$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr(\mathrm{par},w)(t)+(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}(0,a_1)$ at $s$; `hWr4`, for $b=\mathrm{par}$ or $b=\mathrm{par}+P.\mathrm{centralSign}$, the analogous Mellin transform with $(-1)^{b.\mathrm{val}}$ converges for $\mathrm{Re}\,s$ large and equals the archimedean factor of $P.\mathrm{twist}(0,b)$ at $s$; `hWAN`, $WA(\mathrm{par})(n(x)h)=e^{-2\pi i a x}WA(\mathrm{par})(h)$ for unipotent $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hWAZ`, $WA(\mathrm{par})(zI\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{(P.\mathrm{centralSign}).\mathrm{val}}WA(\mathrm{par})(h)$; `hWAK`, $WA(\mathrm{par})(h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(kw(\mathrm{par},\mathrm{default}))(\kappa)\,WA(\mathrm{par})(h)$ for $\kappa$ in the row-isometry subgroup; `hWAt`, $WA(\mathrm{par})(\mathrm{diag}(t,1))=Wr(\mathrm{par},\mathrm{default})(t)$ for $t\in\mathbb R^\times$; `hWAc`, continuity of each $WA(\mathrm{par})$. Finally $w_{0R}\in\mathrm{GL}_2(\mathbb R)$ is the element with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀R`).
--
--   *The place $w_0$, the parameter $P_2$ and the Levi datum $D$.* $w_0$ is a real place of $K$. The hypothesis `hP₂` is the disjunction: either there are real places $w_1,w_2$ with $w_0,w_1,w_2$ pairwise distinct and exhausting the infinite places of $K$, and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$; or there is a complex place $w_C$ such that the infinite places are exactly $w_C$ and $w_0$, and either $kC(w_C)\neq0$ and $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$, or $kC(w_C)=0$ and $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$. $D$ is an archimedean datum of type $P_2$: a function $D.W$ on $2\times2$ real matrices, smooth on the invertible locus, with the unipotent transformation law $D.W(n(x)g)=\psi(x)D.W(g)$ and the central law $D.W(zg)=\mathrm{centralChar}_{P_2}(z)\,|z|\,D.W(g)$, together with a family of entire zeta functions representing the zeta integrals of $D.W$ with archimedean factor $(P_2.\mathrm{twist}(u,a)).\mathrm{archFactor}$, satisfying the functional equation with $\varepsilon$-factor $(P_2.\mathrm{twist}(u,a)).\mathrm{epsilonFactor}$, of finite order in vertical strips, and with the prescribed decay of derivatives at the two ends of the torus. An integer $k_0$ is given, with: `hDW`, $D.W(x r)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(r)\,D.W(x)$ for $r$ in the row-isometry subgroup; `hDE`, $D$ is a Casimir eigenfunction, i.e. $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for every $x$ with $\det x\neq0$; `hDnz`, $D.W$ is not identically zero on $\mathrm{GL}_2(\mathbb R)$; `hk₀min`, in the principal case $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2\pmod 2$, and in the discrete case $k_0=m+1$; `hk₀`, $k_0=0$; and `heven`, in the principal case $aR(w_0)=a_1$. A parity $\mathrm{par}_0\in\mathbb Z/2$ is fixed.
--
--   *The section.* $S\colon M_{2\times3}(\mathbb R)\to\mathbb C$ is, by `hS`, the function
--   $$S(M)=\bigl((M_{00}+iM_{10})-i(M_{01}+iM_{11})\bigr)\,(M_{02}-iM_{12})^1\,\mathrm{gaussian3}(M),\qquad \mathrm{gaussian3}(M)=e^{-\pi\sum_{i,b}M_{ib}^2}.$$
--
--   *The torus profile.* Complex numbers $u_1,u_2$ and $c\in\mathbb Z/2$ are given with $P_2=\mathrm{principal}(u_1,c,u_2,c)$ (`hP₂eq`), and $\rho\in\mathbb C$ is such that (`hρ`) for every $\tau>0$
--   $$D.W\bigl(\mathrm{diag}(\tau,1)\bigr)=\rho\,\tau\cdot 4\int_{0}^{\infty}\bigl(r^{u_1}e^{-\pi r^2}\bigr)\bigl((\tau/r)^{u_2}e^{-\pi(\tau/r)^2}\bigr)\frac{dr}{r}.$$
--
--   *Conclusion.* There exists $\sigma_a\in\mathbb R$ such that for every $s\in\mathbb C$ with $\mathrm{Re}\,s>\sigma_a$ the iterated Lebesgue integral
--   $$\int_{a_2>0}\int_{a_1\in\mathbb R}\Bigl[|\det q|\;WA(\mathrm{par}_0)\bigl(w_{0R}\cdot {}^t q^{-1}\bigr)\cdot \bigl(\mathrm{dualWhittakerFn3}\,\mathcal J\bigr)\bigl(\mathrm{archComponent3}(\iota(\mathrm{archRealGL}(q)))\bigr)\cdot |\det q|^{\,s-1/2}\cdot a_1^{-2}\Bigr]\,da_1\,da_2,$$
--   where the integrand is declared to be $0$ unless $a_1\neq0$ and $a_2>0$, $q=\mathrm{upperUnit}(a_1,0,a_2)=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$, ${}^tq^{-1}=\mathrm{transposeInv}(q)$, $\mathrm{archRealGL}$ is the embedding of $\mathrm{GL}_2(\mathbb R)$ into the adelic $\mathrm{GL}_2$ over $\mathbb Q$ at the real place followed by the inclusion $\iota$ into the adelic $\mathrm{GL}_3$ and by passage to the archimedean component, $\mathrm{dualWhittakerFn3}(W)(g)=W(w_3\cdot{}^tg^{-1})$ for the long Weyl element $w_3$ of $\mathrm{GL}_3$, and $\mathcal J=\mathrm{jacquetVector3}\,D\,(uR(w_0))\,(aR(w_0))\,a\,\psi_\infty\,S$ is the Jacquet vector, the product of $\mathrm{quasiChar}(uR(w_0)+1,aR(w_0))$ evaluated at the determinant of the real matrix of $g$ with $\int_{e\in M_2(\mathbb R)}\mathrm{jacquetIntegrand3}\,D\,(uR(w_0))\,(aR(w_0))\,a\,\psi_\infty\,S\,g\,e$, is equal to
--   $$\Bigl(\varepsilon_\infty\cdot(-1)^{(P.\mathrm{centralSign}).\mathrm{val}}\cdot(-1)^{\#\{w\ \mathrm{complex}\}}\Bigr)\cdot\bigl(\pi\,(-1)^{c.\mathrm{val}}\,\rho\bigr)\cdot\Bigl(\prod_{x}\Gamma_{\mathbb R}\bigl(s+\tfrac12+x\bigr)\Bigr)\Bigl(\prod_{y}\Gamma_{\mathbb C}\bigl(s+\tfrac12+y\bigr)\Bigr).$$
--   Here $\varepsilon_\infty=\mathrm{archRootNumber}$ of the constant families $\mathrm{archOfParamR}\,K\,P$ (the value $P$ at every real place) and $\mathrm{archOfParamC}\,K\,P$ (the value $P.\mathrm{baseChange}$ at every complex place) twisted by $(uR,aR)$ and $(uC,kC)$, that is, the product over the real places $w$ of the $\varepsilon$-factor of $P.\mathrm{twist}(uR(w),aR(w))$ times the product over the complex places $w$ of the $\varepsilon$-factor of $(P.\mathrm{baseChange}).\mathrm{twist}(uC(w),kC(w))$. The first $\Gamma$-product runs over the multiset $\mathrm{twistedGammaR}\,K$ of the dual parameters $(\mathrm{archOfParamR}\,K\,P)^{\vee}$ twisted by $(-uR,aR)$, i.e. the sum over the real places $w$ of the $\gamma_{\mathbb R}$-multiset of $(P^{\vee}).\mathrm{twist}(-uR(w),aR(w))$; the second runs over the multiset $\mathrm{twistedGammaC}\,K$ of the dual parameters $(\mathrm{archOfParamR}\,K\,P)^{\vee}$, $(\mathrm{archOfParamC}\,K\,P)^{\vee}$ twisted by $(-uR,aR)$ at the real places and by $(-uC,-kC)$ at the complex places.
--
--   This is the dual (Weyl-translated) half of the archimedean local computation in the $\mathrm{GL}_3\times\mathrm{GL}_2$ Rankin–Selberg integral attached to the cubic induction, for a weight-one principal parameter $P$ with distinct signs and a weight-zero Levi datum $D$ whose torus profile is a multiplicative Gaussian convolution with parameters $u_1,u_2$; the constant is made explicit as $\pi(-1)^{c}\rho$. It feeds the combined statement [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3), where the primal and dual torus pairs are matched against the complete archimedean $\Gamma$-factor required by the converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile.lean

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
open LanglandsTunnell.CubicInduction
open LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile
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
    (heven : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ → aR w₀ h₀ = a₁)
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ))) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ 1) * gaussian3 M)

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
              = ((archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) * (((Real.pi : ℂ) * (-1 : ℂ) ^ c.val) * ρ)) * (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
                    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod) := by sorry
