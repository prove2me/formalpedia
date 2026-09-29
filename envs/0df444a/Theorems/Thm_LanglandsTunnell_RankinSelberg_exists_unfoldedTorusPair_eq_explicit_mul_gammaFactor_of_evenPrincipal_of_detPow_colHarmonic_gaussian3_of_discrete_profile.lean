-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_discrete_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_discrete_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/148d2389-390e-58af-a733-1e8aec9bc2d2
-- title:
--   Unfolded torus pair equals (-1)ᵇ(π/2)ρ times Γ-product
-- statement:
--   The setting is a number field $K$ of degree $3$ over $\mathbb Q$ (hypothesis `_hdeg`), with $\mathcal O_K$ an integral $\mathcal O_{\mathbb Q}$-algebra.
--
--   **The cubic twist.** A character $\mu\colon \mathbb A_K^\times\to\mathbb C^\times$ is given which is an admissible twist in the sense of `IsAdmissibleTwist`: trivial on the image of $K^\times$, continuous, and of absolute value $1$ everywhere (`_hμ`). The hypothesis `_hns` says that $\mu$ is not of base-change shape: there is no admissible twist $\eta$ of $\mathbb Q$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified (the local component of $\mu$ is trivial on the units of the completed valuation ring) and such that $\eta$ is unramified at $p=\mathfrak P\cap\mathcal O_{\mathbb Q}$, one has $\mu(\varpi_{\mathfrak P})=\eta(\varpi_p)^{f}$, where $\varpi$ denotes the uniformiser idele `uniformizerIdele` and $f$ is the inertia degree `inertiaDeg'` of $\mathfrak P$ over $p$.
--
--   **Archimedean parameters of $\mu$.** Families $u_{\mathbb R}(w)\in\mathbb C$, $a_{\mathbb R}(w)\in\mathbb Z/2$ for the real places $w$ of $K$, and $u_{\mathbb C}(w)\in\mathbb C$, $k_{\mathbb C}(w)\in\mathbb Z$ for the complex places, are given, subject to `huR` and `huC`, which assert `IsArchCompAt` at each infinite place: the archimedean local component of $\mu$ at $w$ sends a unit $x$ of the completion to $\|x\|^{\mathrm{mult}(w)\,u}\,(\iota_w(x)/\|x\|)^{a}$, with $(u,a)=(u_{\mathbb R}(w),(a_{\mathbb R}(w)).\mathrm{val})$ at real places and $(u,a)=(u_{\mathbb C}(w),k_{\mathbb C}(w))$ at complex places.
--
--   **The character $\omega$ of $\mathbb Q$.** A character $\omega\colon\mathbb A_{\mathbb Q}^\times\to\mathbb C^\times$ is given, and `hω` is a conjunction of three clauses: $\omega$ is an admissible twist; for every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ — that is, $p$ is unramified in $K$ and $\mu$ is unramified at every prime of $K$ over $p$ — the character $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals $\mathrm{inducedE3}$ of the coefficient system $\mathrm{inducedCoeff}(K,\mu)$ at $p$, namely minus the degree-$3$ coefficient of the induced Euler polynomial built from the values $\mu(\varpi_{\mathfrak P})$ at unramified $\mathfrak P$ (and $0$ at ramified ones); and, for every re-quantified choice of families $u_{\mathbb R},a_{\mathbb R},u_{\mathbb C},k_{\mathbb C}$ satisfying the same `IsArchCompAt` conditions, at the real place $v$ of $\mathbb Q$ the character $\omega$ satisfies `IsArchCompAt` with exponent $\sum_{w\ \mathrm{real}}u_{\mathbb R}(w)+\sum_{w\ \mathrm{complex}}2u_{\mathbb C}(w)$ and integer parameter $\sum_{w\ \mathrm{real}}(a_{\mathbb R}(w)).\mathrm{val}+\sum_{w\ \mathrm{complex}}(k_{\mathbb C}(w)+1)$, the sums being finite sums over the infinite places of $K$.
--
--   **Adelic frame and measures.** A monoid homomorphism $E\colon(\mathbb A_{\mathbb Q,\infty})^\times\to\mathbb A_{\mathbb Q}^\times$ is given with `hE`: for every $u$, the infinite part of $E(u)$ is $u$ and its finite part is $1$. A rational number $a$ is given with $a\neq 0$ and $a=-1$ (`ha`, `ha1`), a unit $a_\infty$ of the infinite adele ring whose underlying element is the image of $a$ (`haInf`), and an additive character $\psi_\infty$ of $\mathbb A_{\mathbb Q,\infty}$ with $\psi_\infty(x)=\psi_{\mathrm{arch}}(a\,x)$ for the standard archimedean character $\psi_{\mathrm{arch}}$ (`hpsiInf`). Measurable-space and Borel structures on $\mathbb A_{\mathbb Q,\infty}$ and on its unit group are fixed; an additive measure $\nu_{\mathrm{add}}$ is given, equal (`hν_add`) to $|a|^{1/2}$ times the pushforward of Lebesgue measure along the inverse of the ring equivalence `InfiniteAdeleRing.ringEquiv_mixedSpace`, and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb A_{\mathbb Q,\infty})^\times$.
--
--   **The $GL_2$ datum at the place of $\mathbb Q$.** A parameter $P$ of type `RealArchParam` (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$ with $k\ge 1$) is given, with `_hP₁`: if $P$ is principal then $|\mathrm{Re}(u_1-u_2)|<1$. Further data are a weight $k_w(\mathrm{par},w)\in\mathbb Z$, a radial function $W_r(\mathrm{par},w,\cdot)\colon\mathbb R\to\mathbb C$ and a function $W_A(\mathrm{par},\cdot)\colon GL_2(\mathbb R)\to\mathbb C$, indexed by a parity $\mathrm{par}\in\mathbb Z/2$ and an infinite place $w$ of $\mathbb Q$, subject to: `hkw1`, for principal $P$, $k_w(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ where $\mathrm{signShift}(c)$ is $0$ for $c=0$ and $1$ otherwise; `hkw2`, for $P=\mathrm{discrete}(u_0,n)$, $k_w(\mathrm{par},w)=n+1$; `hWr1`, for $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$, the parity law $W_r(\mathrm{par},w,-t)=(-1)^{a_1.\mathrm{val}}W_r(\mathrm{par},w,t)$; `hWr2`, for discrete $P$, $W_r(\mathrm{par},w,t)=0$ for $t<0$; `hWr3`, for $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$, the existence of an abscissa beyond which the Mellin transform of $t\mapsto (W_r(\mathrm{par},w,t)+(-1)^{a_1.\mathrm{val}}W_r(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}(0,a_1)$ at $s$; `hWr4`, for every $\mathrm{par}$ and every $c\in\mathbb Z/2$ with $c=\mathrm{par}$ or $c=\mathrm{par}+P.\mathrm{centralSign}$, the analogous Mellin transform of $t\mapsto (W_r(\mathrm{par},w,t)+(-1)^{c.\mathrm{val}}W_r(\mathrm{par},w,-t))/t$ converges and equals the archimedean factor of $P.\mathrm{twist}(0,c)$ at $s$; `hWAN`, $W_A(\mathrm{par},n(x)h)=e^{-2\pi i a x}W_A(\mathrm{par},h)$ for the unipotent $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hWAZ`, $W_A(\mathrm{par},z\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}W_A(\mathrm{par},h)$ for scalar $z\in\mathbb R^\times$; `hWAK`, $W_A(\mathrm{par},h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_w(\mathrm{par},\mathrm{default}))(\kappa)\,W_A(\mathrm{par},h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb R)$; `hWAt`, $W_A(\mathrm{par},\mathrm{diag}(t,1))=W_r(\mathrm{par},\mathrm{default},t)$ for $t\in\mathbb R^\times$; and `hWAc`, continuity of each $W_A(\mathrm{par},\cdot)$. An element $w_{0,\mathbb R}\in GL_2(\mathbb R)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ is also given.
--
--   **The Levi datum.** A real place $w_0$ of $K$ is fixed, together with a second parameter $P_2$ and the alternative `hP₂`: either $K$ has exactly the three real places $w_0,w_1,w_2$ (pairwise distinct, exhausting the infinite places) and $P_2=\mathrm{principal}(u_{\mathbb R}(w_1),a_{\mathbb R}(w_1),u_{\mathbb R}(w_2),a_{\mathbb R}(w_2))$; or $K$ has a complex place $w_C$ and the infinite places are exactly $w_C$ and $w_0$, and either $k_{\mathbb C}(w_C)\neq 0$ and $P_2=\mathrm{discrete}(u_{\mathbb C}(w_C),|k_{\mathbb C}(w_C)|)$, or $k_{\mathbb C}(w_C)=0$ and $P_2=\mathrm{principal}(u_{\mathbb C}(w_C),0,u_{\mathbb C}(w_C),1)$. Attached to $P_2$ is a datum $D$ of type `ArchDatumR P₂`, that is a function $D.W$ on $2\times2$ real matrices together with the defining clauses of that structure (smoothness on the locus of invertible matrices, the unipotent law $D.W(n(x)g)=\psi(x)D.W(g)$, the central law $D.W(zg)=\chi_{P_2}(z)|z|D.W(g)$ for $z\neq0$, entire auxiliary zeta functions with the Mellin identity $\int \mathrm{zetaIntegrand}=(P_2.\mathrm{twist}(u,a)).\mathrm{archFactor}(s)\cdot\mathrm{zetaEntire}$ beyond an abscissa, the functional equation with $\varepsilon$-factor, finite order in vertical strips, and the prescribed decay of derivatives for large and small $y$; summarised here). An integer $k_0$ is given with: `hDW`, $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, $D$ is a Casimir eigenvector, $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x\neq0$; `hDnz`, $D.W$ is not identically zero; and `hk₀min`, the minimality of $k_0$: if $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, while if $P_2=\mathrm{discrete}(u,m)$ then $k_0=m+1$.
--
--   **Even principal type and the section.** Complex numbers $\nu_1,\nu_2$ and $b\in\mathbb Z/2$ are given with $P=\mathrm{principal}(\nu_1,b,\nu_2,b)$ (`hPev`), together with `hLevi`: if $k_0=0$ and $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $a_1=b$. Integers $n\in\mathbb N$ with $n=k_0$ (`hn`) and $\delta\in\{0,1\}$ (`hδ`) with $\delta\equiv a_{\mathbb R}(w_0)+b\pmod 2$ (`hδpar`) are given, and the section $S$ on $2\times3$ real matrices is (`hS`)
--   $$S(M)=(M_{00}M_{11}-M_{01}M_{10})^{\delta}\,(M_{02}-iM_{12})^{n}\,\exp\Big(-\pi\sum_{i,\beta}M_{i\beta}^2\Big).$$
--
--   **The discrete branch and its torus profile.** Finally $u\in\mathbb C$ and $m\ge1$ are given with $P_2=\mathrm{discrete}(u,m)$ (`hP₂eq`) and $k_0=m+1$ (`hk₀`), and a scalar $\rho\in\mathbb C$ such that (`hρ`) for all $\tau>0$
--   $$D.W\!\begin{pmatrix}\tau&0\\0&1\end{pmatrix}=\rho\cdot 2\,\tau^{\,u+m/2+1}e^{-2\pi\tau},\qquad D.W\!\begin{pmatrix}-\tau&0\\0&1\end{pmatrix}=0 .$$
--
--   **Conclusion.** There exists $\sigma_a\in\mathbb R$ such that for every $s\in\mathbb C$ with $\mathrm{Re}\,s>\sigma_a$, the integral over $e\in\mathbb R^{2\times2}$ (with respect to the canonical volume measure on $\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb R$) of
--   $$\mathrm{quasiChar}\big(u_{\mathbb R}(w_0)+2,\;a_{\mathbb R}(w_0)\big)(\det e)\cdot |\det e|^{-2}\cdot T(e,s)\cdot Z(e,s)$$
--   equals
--   $$\Big((-1)^{b.\mathrm{val}}\frac{\pi}{2}\Big)\rho\cdot\prod_{x}\Gamma_{\mathbb R}\big(s+\tfrac12+x\big)\cdot\prod_{y}\Gamma_{\mathbb C}\big(s+\tfrac12+y\big).$$
--   Here $\mathrm{quasiChar}(u,a)(t)=|t|^{u}$ times $\mathrm{sgn}(t)$ if $a\neq0$ and times $1$ if $a=0$; the two inner factors are the torus integral
--   $$T(e,s)=\int_{\mathbb R}W_r\big(b,\mathrm{default},t\big)\;D.W\Big(\begin{pmatrix}at&0\\0&1\end{pmatrix}e^{-1}\Big)\,|t|^{\,s-1/2}\,t^{-2}\,dt$$
--   and the Godement integral
--   $$Z(e,s)=\int_{0}^{\infty}y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\;\mathrm{godementInner3}\big(\psi_\infty\!\cdot\!\mathrm{shift}(\mathrm{ofReal}\,y),\,S,\,e,\,1\big)\,dy,$$
--   where $\psi_\infty\!\cdot\!\mathrm{shift}(r)$ is the character $x\mapsto\psi_\infty(rx)$, $\mathrm{ofReal}\,y$ is the element of $\mathbb A_{\mathbb Q,\infty}$ with archimedean coordinate $y$, the exponents are $P.\mathrm{centralExponent}=\nu_1+\nu_2$ and $P_2.\mathrm{centralExponent}=2u$, and, with the third argument the identity $3\times3$ matrix,
--   $$\mathrm{godementInner3}(\psi,S,e,1)=\int_{v\in\mathbb R^2}S\Big(e\cdot\begin{pmatrix}1&0&v_0\\0&1&v_1\end{pmatrix}\Big)\,\psi\big(\mathrm{ofReal}(-v_1)\big)\,dv .$$
--   The two products on the right are over the multisets $\mathrm{twistedGammaR}$ and $\mathrm{twistedGammaC}$ formed from the constant family $w\mapsto P$ at real places and its base change $w\mapsto P.\mathrm{baseChange}$ at complex places, twisted by the archimedean parameters of $\mu$; since $P=\mathrm{principal}(\nu_1,b,\nu_2,b)$ these are, explicitly, the multiset $\{\nu_j+u_{\mathbb R}(w)+\mathrm{signShift}(b+a_{\mathbb R}(w))\}$ for $j=1,2$ and $w$ running over the real places of $K$, and the multiset $\{\nu_j+u_{\mathbb C}(w)+|k_{\mathbb C}(w)|/2\}$ for $j=1,2$ and $w$ running over the complex places of $K$.
--
--   The data $E$, $a_\infty$, $\nu_{\mathrm{add}}$, $\nu_{\mathrm{mul}}$, $\omega$, $w_{0,\mathbb R}$ and the functions $k_w$, $W_A$ enter only through the hypotheses listed above; the conclusion itself involves $a$, $b$, $W_r$, $P$, $P_2$, $D$, $\rho$, $S$, $\psi_\infty$ and the archimedean parameters of $\mu$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_discrete_profile.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_discrete_profile
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

    (u : ℂ) (m : ℕ) (hm : 1 ≤ m) (hP₂eq : P₂ = RealArchParam.discrete u m hm) (hk₀ : k₀ = (m : ℤ) + 1)
    (ρ : ℂ)
    (hρ : (∀ τ : ℝ, 0 < τ →
        D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (u + (m : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ)))) ∧
      (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0)) :
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
