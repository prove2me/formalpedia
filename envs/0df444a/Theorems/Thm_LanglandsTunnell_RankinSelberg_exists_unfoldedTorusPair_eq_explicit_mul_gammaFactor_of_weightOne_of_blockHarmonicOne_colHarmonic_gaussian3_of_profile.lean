-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/e992fd66-2f72-5677-b552-a96842d9c95f
-- title:
--   Explicit unfolded archimedean torus pair, weight one, block-harmonic section
-- statement:
--   Throughout, $K$ is a number field whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, together with the hypothesis `_hdeg` that $[K:\mathbb{Q}]=3$.
--
--   *Character data on $K$.* A homomorphism $\mu \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ is given, with `_hμ` asserting that $\mu$ is an admissible twist, i.e. trivial on the principal ideles coming from $K^\times$, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` asserts the non-existence of an admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose underlying prime $p=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ is unramified for $\eta$, one has $\mu(\varpi_{\mathfrak{P}}) = \eta(\varpi_{p})^{f(\mathfrak{P}/p)}$, where $\varpi$ denotes the uniformiser idele and $f$ the inertia degree; here unramifiedness of a character at a place means that it is trivial on the units of the local integers.
--
--   *Archimedean exponents of $\mu$.* Families $uR(w)\in\mathbb{C}$, $aR(w)\in\mathbb{Z}/2$ indexed by the real places of $K$ and $uC(w)\in\mathbb{C}$, $kC(w)\in\mathbb{Z}$ indexed by the complex places are given, and `huR`, `huC` assert that the local component of $\mu$ at $w$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$ with $(u,a)=(uR(w),aR(w).\mathrm{val})$ at real places and $(u,a)=(uC(w),kC(w))$ at complex places.
--
--   *The character $\omega$ on $\mathbb{Q}$.* A homomorphism $\omega\colon(\mathbb{A}_{\mathbb{Q}})^\times\to\mathbb{C}^\times$ is given, and `hω` has three clauses: $\omega$ is an admissible twist; for every prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ which is not a bad place for $(K,\mu)$ (bad meaning ramified in $K$, or with $\mu$ ramified at some prime above $p$), $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, the negative of the degree-$3$ coefficient of the induced Euler polynomial formed from the coefficients $\mu(\varpi_{\mathfrak{P}})$ (set to $0$ at ramified $\mathfrak{P}$); and, for every choice of archimedean exponent data for $\mu$ as above and every real place $v$ of $\mathbb{Q}$, the component of $\omega$ at $v$ has exponent $\sum_{w\ \mathrm{real}} uR(w) + \sum_{w\ \mathrm{complex}} 2\,uC(w)$ and sign exponent $\sum_{w\ \mathrm{real}} aR(w).\mathrm{val} + \sum_{w\ \mathrm{complex}} (kC(w)+1)$ (finite sums).
--
--   *Splitting and additive datum.* A monoid homomorphism $E$ from the infinite idele units of $\mathbb{Q}$ to the full idele units is given with `hE`: the infinite part of $E(u)$ is $u$ and the finite part is $1$. A rational $a$ is given with $a\neq 0$ and $a=-1$, a unit $a_\infty$ of the infinite adeles with $(a_\infty)=\mathrm{alg}(a)$, and an additive character $\psi_\infty$ of the infinite adeles with $\psi_\infty(x)=\psi_{\mathrm{arch}}(\mathrm{alg}(a)\,x)$ for the standard archimedean character $\psi_{\mathrm{arch}}$.
--
--   *Measures.* Besides Borel measurability instances on the infinite adeles and on their units, an additive measure $\nu_{\mathrm{add}}$ is given, required by `hν_add` to be $|a|^{1/2}$ times the push-forward of Lebesgue measure along the inverse of the identification of the infinite adele ring with the mixed space, and a Haar measure $\nu_{\mathrm{mul}}$ on the units.
--
--   *The parameter $P$ and the $\mathbb{Q}$-side Whittaker data.* A real archimedean parameter $P$ is given, with `_hP₁` requiring that if $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $|\mathrm{Re}(u_1-u_2)|<1$. Weights $kw\colon \mathbb{Z}/2\times\{\text{places of }\mathbb{Q}\}\to\mathbb{Z}$, torus functions $Wr(\mathrm{par},w)\colon\mathbb{R}\to\mathbb{C}$ and group functions $WA(\mathrm{par})\colon \mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ are given, subject to: `hkw1`, in the principal case $kw(\mathrm{par},w) = \mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ (as complex numbers, $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$); `hkw2`, in the discrete case $P=\mathrm{discrete}(u_0,n)$ with $n\ge 1$, $kw(\mathrm{par},w)=n+1$; `hWr1`, in the principal case with equal parities $a_1=a_2$ and $\mathrm{par}=a_1$, $Wr(\mathrm{par},w)(-t) = (-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(t)$; `hWr2`, in the discrete case $Wr(\mathrm{par},w)$ vanishes on the negative reals; `hWr3`, in the principal case with $a_1=a_2$ and $\mathrm{par}=a_1+1$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr(\mathrm{par},w)(t)+(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}\,(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$; `hWr4`, for every $\mathrm{par}$ and every $b$ with $b=\mathrm{par}$ or $b=\mathrm{par}+P.\mathrm{centralSign}$, the same symmetrised Mellin transform converges and equals $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$ for $\mathrm{Re}\,s$ large; `hWAN`, $WA(\mathrm{par})(u(x)h) = e^{-2\pi i a x}\,WA(\mathrm{par})(h)$ for the upper unipotent $u(x)$; `hWAZ`, $WA(\mathrm{par})(zh) = |z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}\,WA(\mathrm{par})(h)$ for scalar $z$; `hWAK`, $WA(\mathrm{par})(h\kappa) = \mathrm{archWeightChar}_{\mathbb{R}}(kw(\mathrm{par},\mathrm{default}))(\kappa)\,WA(\mathrm{par})(h)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hWAt`, $WA(\mathrm{par})(\mathrm{diag}(t,1)) = Wr(\mathrm{par},\mathrm{default})(t)$ for $t\in\mathbb{R}^\times$; and `hWAc`, continuity of each $WA(\mathrm{par})$. A further element $w_{0R}\in\mathrm{GL}_2(\mathbb{R})$ is given with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   *The Levi datum at a real place of $K$.* A real place $w_0$ of $K$ is fixed, and a second parameter $P_2$ subject to `hP₂`: either there are real places $w_1,w_2$ with $w_0,w_1,w_2$ pairwise distinct and exhausting the infinite places of $K$, and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$; or there is a complex place $w_C$ such that $w_C,w_0$ exhaust the infinite places, and either $kC(w_C)\neq 0$ and $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$, or $kC(w_C)=0$ and $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$. A datum $D$ of type `ArchDatumR P₂` is given — a function $D.W$ on $2\times 2$ real matrices, smooth on the invertible locus, with the unipotent law $D.W(u(x)g)=\psi(x)D.W(g)$, the central law with central character of $P_2$, entire completed zeta functions whose Mellin integrals factor as $(P_2.\mathrm{twist}\,u\,a).\mathrm{archFactor}(s)$ times an entire function satisfying the epsilon functional equation, together with finite-order and decay estimates — and an integer $k_0$ with: `hDW`, $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, $D$ is a Casimir eigenfunction, i.e. $\mathrm{matrixCasimir}(D.W)(x) = P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ at all $x$ with $\det x\neq 0$; `hDnz`, $D.W$ does not vanish identically; and `hk₀min`, which requires $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \pmod 2$ in the principal case for $P_2$, and $k_0=m+1$ in the discrete case $P_2=\mathrm{discrete}(u,m)$.
--
--   *Normalisations.* The hypothesis `hPw1` states that $P=\mathrm{principal}(u_1',a_1,u_2',a_2)$ for some $u_1',u_2'$ with $a_1\neq a_2$ (weight one); `hk₀` states $k_0=0$; `heven` states that in the principal case $P_2=\mathrm{principal}(u_1',a_1,u_2',a_2)$ one has $aR(w_0)=a_1$. A parity $\mathrm{par}_0\in\mathbb{Z}/2$ is fixed.
--
--   *The section.* A function $S$ on $2\times 3$ real matrices is given, with `hS` prescribing
--   $$S(M) = \bigl((M_{00}+iM_{10}) - i\,(M_{01}+iM_{11})\bigr)\cdot (M_{02}-iM_{12})^{1}\cdot \exp\Bigl(-\pi\sum_{i,b}M_{ib}^2\Bigr).$$
--
--   *The torus profile.* Finally $u_1,u_2\in\mathbb{C}$ and $c\in\mathbb{Z}/2$ are given with `hP₂eq`: $P_2=\mathrm{principal}(u_1,c,u_2,c)$, and $\rho\in\mathbb{C}$ with `hρ`: for all $\tau>0$,
--   $$D.W(\mathrm{diag}(\tau,1)) = \rho\,\tau\cdot\Bigl(4\int_{0}^{\infty} r^{u_1}e^{-\pi r^2}\,(\tau/r)^{u_2}e^{-\pi(\tau/r)^2}\,\frac{dr}{r}\Bigr).$$
--
--   *Conclusion.* There exists $\sigma_a\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\mathrm{Re}\,s>\sigma_a$,
--   $$\int_{e\in M_2(\mathbb{R})} \chi_{uR(w_0)+2,\,aR(w_0)}(\det e)\,|\det e|^{-2}\Bigl(\int_{\mathbb{R}} Wr(\mathrm{par}_0,\mathrm{default})(t)\,D.W\bigl(\mathrm{diag}(at,1)\,e^{-1}\bigr)\,|t|^{s-1/2}\,\frac{dt}{t^{2}}\Bigr)\Bigl(\int_{0}^{\infty} y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,\mathrm{godementInner3}\bigl(\psi_\infty\!\cdot\!\mathrm{ofReal}(y)\bigr)(S)(e)(1)\,dy\Bigr)\,de$$
--   equals
--   $$\bigl(\pi\,(-1)^{c.\mathrm{val}}\,\rho\bigr)\cdot\prod_{x}\Gamma_{\mathbb{R}}\!\left(s+\tfrac12+x\right)\cdot\prod_{x'}\Gamma_{\mathbb{C}}\!\left(s+\tfrac12+x'\right),$$
--   where $x$ runs over the multiset `twistedGammaR K (archOfParamR K P) uR aR`, i.e. the union over the real places $w$ of $K$ of the $\Gamma_{\mathbb{R}}$-shifts of $P$ twisted by $(uR(w),aR(w))$, and $x'$ runs over the multiset `twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC`, i.e. the union of the $\Gamma_{\mathbb{C}}$-shifts of those same twists at the real places together with the $\Gamma_{\mathbb{C}}$-shifts of the base change of $P$ twisted by $(uC(w),kC(w))$ at the complex places. Here $\chi_{u,a}(y)=|y|^{u}$ times the sign of $y$ when $a\neq 0$ and $|y|^u$ when $a=0$, the inner $2\times 2$ integrations are against Lebesgue measure on $\mathbb{R}^{2\times 2}$, $\mathrm{ofReal}(y)$ is the infinite adele all of whose real coordinates equal $y$, and $\mathrm{godementInner3}(\psi)(S)(h)(m) = \int_{v\in\mathbb{R}^2} S\bigl(h\cdot(\,m_{0\bullet}+v_0 m_{2\bullet}\,;\,m_{1\bullet}+v_1 m_{2\bullet}\,)\bigr)\,\psi(\mathrm{ofReal}(-v_1))\,dv$, evaluated at $m=1$.
--
--   This is the archimedean local computation underlying the Rankin–Selberg unfolding in the cubic base-change (Langlands–Tunnell) converse-theorem argument: for a weight-one principal parameter $P$ with distinct parities and a weight-zero Levi datum of $P_2=\mathrm{principal}(u_1,c,u_2,c)$, the unfolded torus integral against the block-harmonic section $S$ is evaluated as the explicit constant $\pi(-1)^{c}\rho$ times the expected product of $\Gamma_{\mathbb{R}}$- and $\Gamma_{\mathbb{C}}$-factors attached to the archimedean parameters of $\mu$ and $P$. It supplies the primal half of the combined statement [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3), where it is matched with the corresponding evaluation of the dual torus integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile
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
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
              = (((Real.pi : ℂ) * (-1 : ℂ) ^ c.val) * ρ) * (((twistedGammaR K (archOfParamR K P) uR aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod) := by sorry
