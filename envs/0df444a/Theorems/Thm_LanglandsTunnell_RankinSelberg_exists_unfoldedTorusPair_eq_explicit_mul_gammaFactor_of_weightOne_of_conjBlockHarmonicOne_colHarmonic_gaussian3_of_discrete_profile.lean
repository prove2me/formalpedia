-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_discrete_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_discrete_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/f7e9f150-ec8e-57b3-97e1-a10ec634c0f9
-- title:
--   Discrete-branch unfolded torus pair equals explicit Gamma-factor product
-- statement:
--   Throughout, $K$ is a number field of degree $3$ over $\mathbb{Q}$ (hypothesis `_hdeg`), equipped with an integral algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$, and $\mu \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ is a character which is an *admissible twist*, i.e. trivial on $K^\times$, continuous, and of absolute value $1$ (hypothesis `_hμ`). The hypothesis `_hns` asserts that no admissible twist $\eta$ of $\mathbb{Q}$ has the property that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and with $\eta$ unramified at $\mathfrak{P} \cap \mathcal{O}_{\mathbb{Q}}$ one has $\mu(\varpi_{\mathfrak{P}}) = \eta(\varpi_{\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}})^{f}$, $f$ the inertia degree and $\varpi$ the uniformiser ideles; here unramifiedness of a character at a finite place means that its local component is trivial on the units of the local integers.
--
--   Archimedean data for $\mu$ are given by families $uR$, $aR$ indexed by the real places and $uC$, $kC$ indexed by the complex places of $K$, with $uR$, $uC$ complex-valued, $aR$ valued in $\mathbb{Z}/2$ and $kC$ integer-valued; the hypotheses `huR`, `huC` state that at each real place $w$ the local component of $\mu$ on $(K_w)^\times$ is $x \mapsto \|x\|^{\mathrm{mult}(w)\,uR(w)}\,(x/\|x\|)^{(aR(w)).\mathrm{val}}$, and similarly at each complex place $w$ with exponents $uC(w)$ and $kC(w)$.
--
--   A character $\omega$ of $(\mathbb{A}_{\mathbb{Q}})^\times$ is given, and `hω` has three conjuncts: $\omega$ is an admissible twist of $\mathbb{Q}$; at every finite place $p$ of $\mathbb{Q}$ which is not bad for $(K,\mu)$ — not ramified in $K$ and with $\mu$ unramified at every prime above $p$ — the character $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals $\mathrm{inducedE3}$ of the family $\mathfrak{P} \mapsto \mu(\varpi_{\mathfrak{P}})$ at $p$, that is minus the degree-$3$ coefficient of the induced Euler polynomial; and, for every choice of archimedean data $(uR,aR,uC,kC)$ for $\mu$ as above, the archimedean component of $\omega$ at each real place $v$ of $\mathbb{Q}$ has exponent $\sum_{w \text{ real}} uR(w) + \sum_{w \text{ complex}} 2\,uC(w)$ and integer parameter $\sum_{w \text{ real}} (aR(w)).\mathrm{val} + \sum_{w \text{ complex}} (kC(w)+1)$.
--
--   Further adelic data: a monoid homomorphism $E$ from the infinite idele units to the full idele units splitting off the infinite part, in the sense that for every $u$ the infinite part of $E(u)$ is $u$ and the finite part of $E(u)$ is $1$ (`hE`); a rational number $a \neq 0$ which is moreover equal to $-1$ (`ha`, `ha1`); a unit $a_{\infty}$ of the infinite adeles whose underlying element is the image of $a$ (`haInf`); an additive character $\psi_{\infty}$ of the infinite adeles with $\psi_{\infty}(x) = \psi_{\mathrm{arch}}(a x)$ for the standard archimedean character (`hpsiInf`); measurable and Borel structures on the infinite adeles and on their unit group; a measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the mixed-space ring equivalence (`hν_add`); and a Haar measure $\nu_{\mathrm{mul}}$ on the unit group.
--
--   On the $\mathbb{Q}$ side, $P$ is a real archimedean parameter (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$ with $k \geq 1$), subject to `_hP₁`: in the principal case $|\mathrm{Re}(u_1-u_2)| < 1$. Whittaker data attached to $P$ consist of weights $kw \colon \mathbb{Z}/2 \times \{\text{places of } \mathbb{Q}\} \to \mathbb{Z}$, torus functions $Wr(\mathrm{par},w,\cdot) \colon \mathbb{C}\to\mathbb{C}$ and functions $WA(\mathrm{par}) \colon GL_2(\mathbb{R}) \to \mathbb{C}$, with the following hypotheses. The weight normalisations `hkw1`, `hkw2` require $(kw\,\mathrm{par}\,w : \mathbb{C}) = \mathrm{signShift}(a_1+\mathrm{par}) + \mathrm{signShift}(a_2+\mathrm{par})$ when $P = \mathrm{principal}(u_1,a_1,u_2,a_2)$, and $kw\,\mathrm{par}\,w = n+1$ when $P = \mathrm{discrete}(u_0,n)$, at every real place $w$. The torus hypotheses are: `hWr1`, parity $Wr(\mathrm{par},w,-t) = (-1)^{a_1.\mathrm{val}} Wr(\mathrm{par},w,t)$ when $P = \mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par} = a_1$; `hWr2`, vanishing on $t<0$ in the discrete case; `hWr3`, for $P = \mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par} = a_1+1$ the existence of an abscissa beyond which the Mellin transform of $t \mapsto (Wr(\mathrm{par},w,t) + (-1)^{a_1.\mathrm{val}} Wr(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$ at $s$; and `hWr4`, for every $b$ with $b = \mathrm{par}$ or $b = \mathrm{par} + P.\mathrm{centralSign}$, the analogous Mellin convergence with value the archimedean factor of $P.\mathrm{twist}\,0\,b$ at $s$. The group-theoretic hypotheses on $WA$ are: `hWAN`, $WA(\mathrm{par})(u(x)h) = e^{-2\pi i a x} WA(\mathrm{par})(h)$ for unipotent $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hWAZ`, the central law $WA(\mathrm{par})(z\cdot h) = |z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}\,WA(\mathrm{par})(h)$ for scalar matrices; `hWAK`, right equivariance $WA(\mathrm{par})(h\kappa) = \mathrm{archWeightChar}_{\mathbb{R}}(kw\,\mathrm{par}\,\mathrm{default})(\kappa)\,WA(\mathrm{par})(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, the restriction to the torus $\mathrm{diag}(t,1)$ is $Wr(\mathrm{par},\mathrm{default},t)$; and `hWAc`, continuity of each $WA(\mathrm{par})$. An element $w_{0R}$ of $GL_2(\mathbb{R})$ with underlying matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ is also given.
--
--   Finally, $w_0$ is a real place of $K$ and $P_2$ a real archimedean parameter constrained by `hP₂`: either $K$ has exactly three infinite places $w_0,w_1,w_2$, all real and pairwise distinct, and $P_2 = \mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$; or $K$ has exactly the two infinite places $w_0$ and a complex place $w_C$, and then either $kC(w_C) \neq 0$ and $P_2 = \mathrm{discrete}(uC(w_C),|kC(w_C)|)$, or $kC(w_C) = 0$ and $P_2 = \mathrm{principal}(uC(w_C),0,uC(w_C),1)$. Attached to $P_2$ is an archimedean datum $D$ (a Whittaker function $D.W$ on $2\times 2$ real matrices, smooth on the invertible locus, with unipotent and central transformation laws for $P_2$, together with its entire zeta functions, integrability, functional equation, order and decay data) and an integer $k_0$, subject to: `hDW`, right equivariance of $D.W$ under `rowIsometrySubgroup₀ ℝ` by the weight character of $k_0$; `hDE`, the Casimir eigenvalue equation $\mathrm{matrixCasimir}(D.W)(x) = P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x \neq 0$; `hDnz`, $D.W$ is not identically zero; and `hk₀min`, which in the principal case $P_2 = \mathrm{principal}(u_1,a_1,u_2,a_2)$ forces $k_0 \in \{0,1\}$ with $k_0 \equiv a_1+a_2 \pmod 2$, and in the discrete case $P_2 = \mathrm{discrete}(u,m)$ forces $k_0 = m+1$. In addition: `hPw1` requires $P = \mathrm{principal}(u_1,a_1,u_2,a_2)$ with $a_1 \neq a_2$; `hk₀` requires $1 \leq k_0$; $n$ is a natural number with $n = k_0-1$; $\mathrm{par}_0 \in \mathbb{Z}/2$ is arbitrary; and $S$ is the function on $2\times 3$ real matrices given by `hS` as
--   $$S(M) = \big((M_{00}-iM_{10}) - i(M_{01}-iM_{11})\big)\,(M_{02}-iM_{12})^n\,e^{-\pi\sum_{i,b} M_{ib}^2}.$$
--   The discrete branch is then pinned: $u \in \mathbb{C}$, $k \geq 1$, $P_2 = \mathrm{discrete}(u,k)$, $k_0 = k+1$, $n = k$, and a scalar $\rho$ is given for which `hρ` asserts the one-sided torus profile $D.W(\mathrm{diag}(\tau,1)) = \rho\cdot 2\,\tau^{u+k/2+1}e^{-2\pi\tau}$ and $D.W(\mathrm{diag}(-\tau,1)) = 0$ for all $\tau > 0$.
--
--   The conclusion asserts the existence of a real abscissa $\sigma_1$ such that for every $s$ with $\mathrm{Re}\,s > \sigma_1$ the integral over $e \in \mathbb{R}^{2\times 2}$, with respect to Lebesgue measure on the entries, of
--   $$|\det e|^{uR(w_0)+2}\,\epsilon(\det e)\,|\det e|^{-2}\cdot\Big(\int_{\mathbb{R}} Wr(\mathrm{par}_0,\mathrm{default},t)\;D.W\big(\mathrm{diag}(at,1)\,e^{-1}\big)\,|t|^{s-1/2}\,t^{-2}\,dt\Big)\cdot\Big(\int_0^{\infty} y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,\mathrm{godementInner3}\big(\psi_{\infty}\!\cdot\! y,\,S,\,e,\,1\big)\,dy\Big)$$
--   equals
--   $$\Big((-1)^{(aR(w_0)).\mathrm{val}+1}\,\frac{\pi}{2}\,\rho\Big)\cdot \prod_{x} \Gamma_{\mathbb{R}}\!\big(s+\tfrac12+x\big)\cdot\prod_{x} \Gamma_{\mathbb{C}}\!\big(s+\tfrac12+x\big).$$
--   Here the quasicharacter factor is $\mathrm{quasiChar}(uR(w_0)+2, aR(w_0))$ evaluated at $\det e$, so $\epsilon(y) = 1$ if $aR(w_0) = 0$ and $\epsilon(y) = \mathrm{sign}(y)$ otherwise; $\mathrm{godementInner3}$ of the multiplicatively shifted character $\psi_{\infty}$ by the infinite adele attached to $y$, the Schwartz function $S$, the matrix $e$ and $m = 1$ is the integral over $v \in \mathbb{R}^2$ of $S$ applied to $e$ times the $2\times 3$ matrix with rows $(m_{0b}+v_0 m_{2b})_b$ and $(m_{1b}+v_1 m_{2b})_b$, against the character evaluated at the infinite adele attached to $-v_1$. The first product runs over the multiset $\mathrm{twistedGammaR}$ of $K$ for the constant real family $w \mapsto P$ and the data $uR$, $aR$, namely the sum over the real places $w$ of the real gamma-shifts of $P.\mathrm{twist}(uR(w), aR(w))$; the second runs over the multiset $\mathrm{twistedGammaC}$, namely the sum over the real places $w$ of the complex gamma-shifts of $P.\mathrm{twist}(uR(w),aR(w))$ together with the sum over the complex places $w$ of the complex gamma-shifts of the base change of $P$ twisted by $(uC(w), kC(w))$; under `hPw1` the first of these two contributions is empty.
--
--   This is the archimedean local computation of the unfolded torus pair arising from Godement's section of the $2\times 3$ Rankin–Selberg integral on the discrete-series branch of the Levi parameter $P_2$, carried out for the weight-one principal parameter $P$ with distinct parities: the unfolded integral is evaluated as an explicit constant $(-1)^{a_0+1}(\pi/2)\rho$ times the complete product of $\Gamma_{\mathbb{R}}$- and $\Gamma_{\mathbb{C}}$-factors predicted for the cubic induction of $\mu$. It feeds the companion statement combining the unfolded and dual torus pairs, which supplies the archimedean input to the converse theorem used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_discrete_profile.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_discrete_profile
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
    (u : ℂ) (k : ℕ) (hk : 1 ≤ k) (hP₂eq : P₂ = RealArchParam.discrete u k hk)
    (hk0k : k₀ = (k : ℤ) + 1) (hnk : n = k)
    (ρ : ℂ)
    (hρ : (∀ τ : ℝ, 0 < τ →
        D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (u + (k : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ)))) ∧
      (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0)) :
    ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
              = (((-1 : ℂ) ^ ((aR w₀ h₀).val + 1) * ((Real.pi : ℂ) / 2)) * ρ) * (((twistedGammaR K (archOfParamR K P) uR aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod) := by sorry
