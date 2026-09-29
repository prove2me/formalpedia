-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightOne_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightOne_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/36298ee9-d4ae-5870-abbe-bac069a51075
-- title:
--   Explicit unfolded torus pair: (-1)ᵇ(π/2)ρ times the twisted Γ-product
-- statement:
--   **Global setting.** Let $K$ be a number field with $[K:\mathbb Q]=3$ (`_hdeg`), $\mathcal O_K$ an integral $\mathcal O_{\mathbb Q}$-algebra, and let $\mu\colon(\mathbb A_K)^\times\to\mathbb C^\times$ be an admissible twist (`_hμ`: trivial on the image of $K^\times$, continuous, and of absolute value $1$ everywhere). The hypothesis `_hns` asserts that $\mu$ admits no descent: there is no admissible twist $\eta$ of $\mathbb Q$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified (its local character is trivial on the local units) and with $\eta$ unramified at $\mathfrak p=\mathfrak P\cap\mathcal O_{\mathbb Q}$, the value of $\mu$ on the uniformiser idele at $\mathfrak P$ equals the value of $\eta$ on the uniformiser idele at $\mathfrak p$ raised to the inertia degree `inertiaDeg'` of $\mathfrak P$ over $\mathfrak p$.
--
--   **Archimedean components of $\mu$.** Families $uR,aR$ indexed by the real places and $uC,kC$ indexed by the complex places of $K$ are given, with `huR` and `huC` asserting `IsArchCompAt`: at a real place $w$ the archimedean local component of $\mu$ is $x\mapsto\|x\|^{m_w\,uR(w)}\bigl(\iota_w(x)/\|x\|\bigr)^{(aR(w)).\mathrm{val}}$, and at a complex place $w$ it is $x\mapsto\|x\|^{m_w\,uC(w)}(\iota_w(x)/\|x\|)^{kC(w)}$.
--
--   **The descended character $\omega$.** A character $\omega$ of $(\mathbb A_{\mathbb Q})^\times$ is given together with the three clauses of `hω`: $\omega$ is an admissible twist of $\mathbb Q$; at every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ — that is, $p$ is unramified in $K$ and $\mu$ is unramified at every prime of the fibre above $p$ — the character $\omega$ is unramified at $p$ and its Euler coefficient equals $-$(the degree-$3$ coefficient of the induced Euler polynomial) of the coefficient system $\mathfrak P\mapsto\mu(\text{uniformiser idele at }\mathfrak P)$ (zero at ramified $\mathfrak P$); and, for every quadruple $(uR,aR,uC,kC)$ satisfying the same `IsArchCompAt` conditions, the archimedean component of $\omega$ at the real place of $\mathbb Q$ has exponent $\sum_{w\ \mathrm{real}}uR(w)+\sum_{w\ \mathrm{cplx}}2\,uC(w)$ and integer parameter $\sum_{w\ \mathrm{real}}(aR(w)).\mathrm{val}+\sum_{w\ \mathrm{cplx}}(kC(w)+1)$ (finite sums).
--
--   **Adelic normalisations.** A monoid homomorphism $E$ from the units of the infinite adele ring of $\mathbb Q$ to the ideles, splitting the infinite part and having trivial finite part (`hE`); a rational $a\neq0$ with $a=-1$ (`ha`, `ha1`); a unit $a_\infty$ of the infinite adele ring with underlying element the image of $a$ (`haInf`); the additive character $\psi_\infty$ with $\psi_\infty(x)=\psi_{\mathrm{arch}}(a\,x)$ for the standard archimedean character (`hpsiInf`); measurable and Borel structures on the infinite adele ring and on its unit group; an additive measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the transport of Lebesgue measure along the inverse of the mixed-space identification (`hν_add`); and a Haar measure $\nu_{\mathrm{mul}}$ on the units.
--
--   **The parameter $P$ and the Whittaker package for $\omega$.** A real archimedean parameter $P$ is given, subject to `_hP₁` (if $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $|\mathrm{Re}(u_1-u_2)|<1$), together with data $kw$ (weights), $Wr$ (torus profiles) and $WA$ (functions on $\mathrm{GL}_2(\mathbb R)$) indexed by a parity in $\mathbb Z/2$, and the following hypotheses. `hkw1`: in the principal case $kw(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$; `hkw2`: in the discrete case $P=\mathrm{discrete}(u_0,n')$, $kw(\mathrm{par},w)=n'+1$. `hWr1`: for $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$, $Wr(\mathrm{par},w,-t)=(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w,t)$; `hWr2`: in the discrete case $Wr(\mathrm{par},w,t)=0$ for $t<0$; `hWr3`: for $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$ there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr(\mathrm{par},w,t)+(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}\cdot(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$; `hWr4`: for every $\beta\in\mathbb Z/2$ with $\beta=\mathrm{par}$ or $\beta=\mathrm{par}+P.\mathrm{centralSign}$ the analogous Mellin transform, formed with $(-1)^{\beta.\mathrm{val}}$, converges in a right half-plane and equals $(P.\mathrm{twist}\,0\,\beta).\mathrm{archFactor}(s)$. For $WA$: `hWAN` the unipotent law $WA(\mathrm{par},u(x)h)=e^{-2\pi i a x}WA(\mathrm{par},h)$; `hWAZ` the central law with factor $|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}$; `hWAK` right equivariance under `rowIsometrySubgroup₀ ℝ` by the character `archWeightCharℝ` of weight $kw(\mathrm{par},\mathrm{default})$; `hWAt` the identification $WA(\mathrm{par},\mathrm{diagOne}(t))=Wr(\mathrm{par},\mathrm{default},t)$ on the torus; `hWAc` continuity. A matrix $w_{0R}\in\mathrm{GL}_2(\mathbb R)$ with underlying matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ is also given (`hw₀R`).
--
--   **The companion parameter and its Whittaker datum.** A real place $w_0$ of $K$ is fixed, and a real archimedean parameter $P_2$ subject to `hP₂`: either $K$ has exactly the three real places $w_0,w_1,w_2$ (pairwise distinct and exhausting the infinite places) and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$; or $K$ has exactly the places $w_C$ (complex) and $w_0$, and either $kC(w_C)\neq0$ and $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$, or $kC(w_C)=0$ and $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$. Further, $D$ is an `ArchDatumR P₂`, that is a real archimedean Whittaker datum for $P_2$: a function $D.W$ on $2\times2$ real matrices, smooth on the invertible locus, with the unipotent law $D.W(u(x)g)=\psi(x)D.W(g)$, the central law $D.W(zg)=\mathrm{centralChar}_{P_2}(z)\,|z|\,D.W(g)$, an entire completed zeta function matching the torus zeta integrals with archimedean factor $(P_2.\mathrm{twist}\,u\,a).\mathrm{archFactor}$, the archimedean functional equation with epsilon factor, finite order in vertical strips, and decay bounds near $0$ and $\infty$. An integer $k_0$ is given with `hDW`: $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`: $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for $\det x\neq0$; `hDnz`: $D.W$ does not vanish identically; and `hk₀min`: in the principal case $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, in the discrete case $k_0=m+1$.
--
--   **Even type and the Gaussian section.** Complex numbers $\nu_1,\nu_2$ and $b\in\mathbb Z/2$ are given with `hPev`: $P=\mathrm{principal}(\nu_1,b,\nu_2,b)$; `hLevi`: if $k_0=0$ and $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $a_1=b$. A natural number $n$ with $(n:\mathbb Z)=k_0$, and $\delta\in\{0,1\}$ (`hδ`) with $\delta\equiv aR(w_0)+b\pmod2$ (`hδpar`). The section $S$ on $2\times3$ real matrices is given by `hS`:
--   $$S(M)=(M_{00}M_{11}-M_{01}M_{10})^{\delta}\,\bigl(M_{02}-iM_{12}\bigr)^{n}\,\exp\Bigl(-\pi\sum_{i,\beta}M_{i\beta}^2\Bigr).$$
--
--   **Branch hypotheses.** Finally $P_2=\mathrm{principal}(u_1,c_1,u_2,c_2)$ (`hP₂eq`) with $c_1\neq c_2$ (`hc`) and $k_0=1$ (`hk₀`), and a constant $\rho\in\mathbb C$ such that for every $b'\in\mathbb Z/2$ and every $\tau>0$ (`hρ`)
--   $$D.W(\mathrm{diagOne}(\tau))+(-1)^{b'.\mathrm{val}}D.W(\mathrm{diagOne}(-\tau))=\rho\,\tau\cdot 4\!\!\int_{0}^{\infty}\! r^{\,u_1+\mathrm{signShift}(c_1+b')}e^{-\pi r^2}\,(\tau/r)^{\,u_2+\mathrm{signShift}(c_2+b')}e^{-\pi(\tau/r)^2}\,\frac{dr}{r},$$
--   where $\mathrm{diagOne}(y)=\begin{pmatrix}y&0\\0&1\end{pmatrix}$.
--
--   **Conclusion.** There exists $\sigma_a\in\mathbb R$ such that for every $s\in\mathbb C$ with $\mathrm{Re}\,s>\sigma_a$ the integral over $e\in M_2(\mathbb R)$ (Lebesgue measure on the four real coordinates) of
--   $$\mathrm{quasiChar}\bigl(uR(w_0)+2,\;aR(w_0)\bigr)(\det e)\cdot |\det e|^{-2}\cdot T(e,s)\cdot M(e,s)$$
--   equals
--   $$\Bigl((-1)^{b.\mathrm{val}}\tfrac{\pi}{2}\,\rho\Bigr)\cdot\Bigl(\prod_{x\in\Gamma_{\mathbb R}\text{-multiset}}\Gamma_{\mathbb R}\bigl(s+\tfrac12+x\bigr)\Bigr)\cdot\Bigl(\prod_{x\in\Gamma_{\mathbb C}\text{-multiset}}\Gamma_{\mathbb C}\bigl(s+\tfrac12+x\bigr)\Bigr).$$
--   Here $\mathrm{quasiChar}(u,a)(y)=|y|^{u}$ times $\mathrm{sign}(y)$ if $a\neq0$ and times $1$ if $a=0$; the two inner factors are the torus integral
--   $$T(e,s)=\int_{\mathbb R}Wr(b,\mathrm{default},t)\;D.W\bigl(\mathrm{diagOne}(a\,t)\cdot e^{-1}\bigr)\;|t|^{\,s-1/2}\;t^{-2}\,dt$$
--   and the Godement–Tate factor
--   $$M(e,s)=\int_{0}^{\infty}y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\;\mathrm{godementInner3}\bigl(\psi_\infty^{(y)},S,e,1\bigr)\,dy,$$
--   where $\psi_\infty^{(y)}$ is the multiplicative shift of $\psi_\infty$ by the image of $y$ in the infinite adele ring, and, for the identity $3\times3$ matrix,
--   $$\mathrm{godementInner3}\bigl(\psi,S,e,1\bigr)=\int_{\mathbb R^2}S\Bigl(e\cdot\begin{pmatrix}1&0&v_0\\0&1&v_1\end{pmatrix}\Bigr)\,\psi\bigl(-v_1\bigr)\,dv .$$
--   With $P=\mathrm{principal}(\nu_1,b,\nu_2,b)$ the two shift multisets are the twisted ones attached to $\Pi(\mu)$: `twistedGammaR` is the multiset $\{\nu_1+uR(w)+\mathrm{signShift}(b+aR(w)),\ \nu_2+uR(w)+\mathrm{signShift}(b+aR(w))\}$ summed over the real places $w$ of $K$, and `twistedGammaC` is the multiset $\{\nu_1+uC(w)+|kC(w)|/2,\ \nu_2+uC(w)+|kC(w)|/2\}$ summed over the complex places $w$ of $K$, the real places contributing nothing to the latter. The central exponents are $P.\mathrm{centralExponent}=\nu_1+\nu_2$ and $P_2.\mathrm{centralExponent}=u_1+u_2$.
--
--   This is the primal half of the archimedean Rankin–Selberg torus-pair evaluation in the Langlands–Tunnell converse-theorem input for a cubic field: on the branch where the companion real parameter $P_2$ is principal with distinct parities and the Whittaker datum $D$ has weight $k_0=1$, the unfolded archimedean zeta integral of the determinant-power, column-harmonic Gaussian section is identified with the completed $\Gamma$-factor of the induced parameter, with the constant made explicit as $(-1)^{b}(\pi/2)\rho$. It feeds the combined statement [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightOne_profile.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightOne_profile
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
    (ν₁ ν₂ : ℂ) (b : ZMod 2) (hPev : P = RealArchParam.principal ν₁ b ν₂ b)
    (hLevi : k₀ = 0 → ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = b)
    (n : ℕ) (hn : (n : ℤ) = k₀)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = aR w₀ h₀ + b)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)

    (u₁ u₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c₁ u₂ c₂) (hc : c₁ ≠ c₂) (hk₀ : k₀ = 1)
    (ρ : ℂ)
    (hρ : ∀ (b' : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b'.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁ + signShift (c₁ + b')) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (u₂ + signShift (c₂ + b')) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ))) :
    ∃ σa : ℝ, (∀ s : ℂ, σa < s.re →
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr b default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
              = (((-1 : ℂ) ^ b.val * ((Real.pi : ℂ) / 2)) * ρ) * (((twistedGammaR K (archOfParamR K P) uR aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) := by sorry
