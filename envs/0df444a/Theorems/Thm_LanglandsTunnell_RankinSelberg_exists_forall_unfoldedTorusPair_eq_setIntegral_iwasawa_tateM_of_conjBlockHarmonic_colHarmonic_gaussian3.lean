-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_conjBlockHarmonic_colHarmonic_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_conjBlockHarmonic_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/d2b5b138-cc69-5883-8a02-4e9631c48ba2
-- title:
--   Iwasawa–Tate evaluation of an unfolded archimedean torus integral
-- statement:
--   Throughout, $K$ is a number field with $\operatorname{finrank}_{\mathbb Q} K = 3$ (hypothesis `_hdeg`), whose ring of integers is an integral $\mathcal O_{\mathbb Q}$-algebra.
--
--   **Global character data.** A continuous homomorphism $\mu\colon (\mathbb A_K)^\times\to\mathbb C^\times$ is given which is an *admissible twist* (`_hμ`), i.e. it is trivial on the principal ideles coming from $K^\times$, continuous, and of absolute value $1$ at every idele. The hypothesis `_hns` asserts that $\mu$ does not come from $\mathbb Q$ in the following sense: there is no admissible twist $\eta$ of $\mathbb Q$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and whose underlying prime $p=\mathfrak P\cap\mathcal O_{\mathbb Q}$ is such that $\eta$ is unramified at $p$, one has $\mu(\varpi_{\mathfrak P}) = \eta(\varpi_{p})^{f}$, where $\varpi$ denotes the uniformiser idele `uniformizerIdele` and $f$ is the inertia degree `inertiaDeg'` of $\mathfrak P$ over $p$. (Unramifiedness at a finite place means that the local character of $\mu$ is trivial on the units of the local integers.) Archimedean data for $\mu$ are fixed: functions $uR$, $aR$ on the real places with values in $\mathbb C$ and $\mathbb Z/2$, and $uC$, $kC$ on the complex places with values in $\mathbb C$ and $\mathbb Z$, such that (`huR`, `huC`) at every real place $w$ the archimedean local component of $\mu$ is $x\mapsto \|x\|^{\,\mathrm{mult}(w)\,uR(w)}\,(x/\|x\|)^{aR(w).\mathrm{val}}$ and at every complex place $w$ it is $x\mapsto \|x\|^{\,\mathrm{mult}(w)\,uC(w)}\,(x/\|x\|)^{kC(w)}$, in the sense of `IsArchCompAt`.
--
--   A homomorphism $\omega\colon (\mathbb A_{\mathbb Q})^\times\to\mathbb C^\times$ is given, subject to the three clauses of `hω`: $\omega$ is an admissible twist; for every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ — bad meaning that $p$ is ramified in $K$ or that $\mu$ is ramified at some prime above $p$ — $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, minus the degree-$3$ coefficient of the induced Euler polynomial built from the local data $\mathfrak P\mapsto\mu(\varpi_{\mathfrak P})$ (set to $0$ at ramified $\mathfrak P$); and, for all archimedean data $uR,aR,uC,kC$ satisfying the two `IsArchCompAt` conditions above, the archimedean component of $\omega$ at each real place $v$ of $\mathbb Q$ has parameters $\big(\sum_{w\text{ real}}uR(w)+\sum_{w\text{ complex}}2\,uC(w),\ \sum_{w\text{ real}}aR(w).\mathrm{val}+\sum_{w\text{ complex}}(kC(w)+1)\big)$, the sums being finite sums over the places of $K$.
--
--   **Adelic normalisations.** A homomorphism $E\colon (\mathbb A_{\mathbb Q,\infty})^\times\to(\mathbb A_{\mathbb Q})^\times$ is given with (`hE`) infinite part the identity and finite part trivial. A rational number $a$ is given with $a\neq 0$ (`ha`) and $a=-1$ (`ha1`), together with a unit $a_\infty$ of the infinite adeles whose underlying element is the image of $a$ (`haInf`), and an additive character $\psi_\infty$ of $\mathbb A_{\mathbb Q,\infty}$ with $\psi_\infty(x)=\psi_{\mathrm{arch}}(a x)$ for the standard archimedean character (`hpsiInf`). Measures: $\nu_{\mathrm{add}}$ on $\mathbb A_{\mathbb Q,\infty}$ is $|a|^{1/2}$ times the pushforward of Lebesgue volume under the inverse of the ring equivalence with the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb A_{\mathbb Q,\infty})^\times$; the infinite adele ring and its unit group carry measurable structures which are Borel.
--
--   **The parameter $P$ and the $\mathrm{GL}_2/\mathbb Q$ Whittaker data.** $P$ is a real archimedean parameter, either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$ with $k\ge 1$; `_hP₁` requires $|\mathrm{Re}(u_1-u_2)|<1$ in the principal case. Functions $kw\colon \mathbb Z/2\times\mathrm{InfinitePlace}\,\mathbb Q\to\mathbb Z$, $Wr\colon \mathbb Z/2\times\mathrm{InfinitePlace}\,\mathbb Q\to(\mathbb R\to\mathbb C)$ and $WA\colon\mathbb Z/2\to(\mathrm{GL}_2(\mathbb R)\to\mathbb C)$ are given, subject to: `hkw1`, in the principal case $kw(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ (with $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$), and `hkw2`, in the discrete case $kw(\mathrm{par},w)=k+1$; `hWr1`, when $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$, the evenness/oddness $Wr(\mathrm{par},w)(-t)=(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(t)$; `hWr2`, in the discrete case $Wr(\mathrm{par},w)$ vanishes on $t<0$; `hWr3`, when $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr(\mathrm{par},w)(t)+(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$ at $s$; and `hWr4`, for every $b$ equal to $\mathrm{par}$ or to $\mathrm{par}+P.\mathrm{centralSign}$, the analogous Mellin transform with $(-1)^{b.\mathrm{val}}$ converges for $\mathrm{Re}\,s$ large and equals the archimedean factor of $P.\mathrm{twist}\,0\,b$ at $s$. The function $WA$ satisfies: `hWAN`, $WA(\mathrm{par})(u(x)h)=e^{-2\pi i a x}WA(\mathrm{par})(h)$ for the upper unipotent $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hWAZ`, $WA(\mathrm{par})(zh)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}WA(\mathrm{par})(h)$ for scalar matrices $z$; `hWAK`, $WA(\mathrm{par})(h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(kw(\mathrm{par},\mathrm{default}))(\kappa)\,WA(\mathrm{par})(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, $WA(\mathrm{par})(\mathrm{diag}(t,1))=Wr(\mathrm{par},\mathrm{default})(t)$ for $t\in\mathbb R^\times$; and `hWAc`, continuity of each $WA(\mathrm{par})$. An element $w_{0R}\in\mathrm{GL}_2(\mathbb R)$ with underlying matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ is given (`hw₀R`).
--
--   **The place $w_0$, the parameter $P_2$ and the Levi datum $D$.** $w_0$ is a real place of $K$ (`h₀`), and $P_2$ is a real archimedean parameter subject to `hP₂`: either $K$ has exactly the three distinct real places $w_0,w_1,w_2$ and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$; or $K$ has exactly the places $w_0$ and one complex place $w_C$, and either $kC(w_C)\neq 0$ and $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$, or $kC(w_C)=0$ and $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$. Further, $D$ is an archimedean datum `ArchDatumR P₂`: a function $D.W$ on $2\times2$ real matrices, smooth on the locus of nonvanishing determinant, with the unipotent law $D.W(u(x)g)=\psi(x)D.W(g)$, the central law $D.W(zg)=P_2.\mathrm{centralChar}(z)\,|z|\,D.W(g)$ for $z\neq0$, together with an entire completed zeta function $\mathrm{zetaEntire}$, an abscissa beyond which the zeta integrand $y\mapsto D.W(\mathrm{diag}(y,1)g)\,\mathrm{quasiChar}(u,a)(y)|y|^{s-1}|y|^{-1}$ is integrable with integral $(P_2.\mathrm{twist}\,u\,a).\mathrm{archFactor}(s)\cdot\mathrm{zetaEntire}(g,u,a,s)$, the functional equation relating $\mathrm{zetaEntire}$ at $(\text{Weyl}\cdot g,-(u+P_2.\mathrm{centralExponent}),a+P_2.\mathrm{centralSign},1-s)$ to $(P_2.\mathrm{twist}\,u\,a).\mathrm{epsilonFactor}$ times $\mathrm{zetaEntire}(g,u,a,s)$, finite order in vertical strips, and decay bounds for the derivatives at large and small $|y|$. An integer $k_0$ is given with: `hDW`, $D.W(xr)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(r)\,D.W(x)$ for $r\in$ `rowIsometrySubgroup₀ ℝ`; `hDE`, the Casimir eigenequation $-\big(\tfrac14\partial_H^2-\tfrac12\partial_H+\partial_E\partial_{F^-}\big)D.W = P_2.\mathrm{laplaceEigenvalue}\cdot D.W$ at every invertible matrix, the eigenvalue being $\tfrac14-\big(\tfrac{u_1-u_2}{2}\big)^2$ in the principal case and $\tfrac{1-k^2}{4}$ in the discrete case; `hDnz`, $D.W$ is not identically zero; and `hk₀min`, $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \pmod 2$ when $P_2$ is principal, and $k_0=m+1$ when $P_2=\mathrm{discrete}(u,m)$.
--
--   **The section.** A parity $\mathrm{par}_0\in\mathbb Z/2$, natural numbers $m,n,\delta$ with $\delta\in\{0,1\}$ (`hδ`), a sign $\varepsilon'=\pm1$ (`hε'`), and the function $S$ on $2\times3$ real matrices given by (`hS`)
--   $$S(M)=(M_{00}M_{11}-M_{01}M_{10})^{\delta}\,\big((M_{00}-iM_{10})-i(M_{01}-iM_{11})\big)^{m}\,\big(M_{02}+\varepsilon' i M_{12}\big)^{n}\,e^{-\pi\sum_{i<2}\sum_{b<3}M_{ib}^2}.$$
--
--   **Conclusion.** There exists $\sigma_1\in\mathbb R$ such that for every $s\in\mathbb C$ with $\mathrm{Re}\,s>\sigma_1$ the following equality of integrals holds. Write $\chi(y)=|y|^{\,uR(w_0)+2}\cdot(1$ if $aR(w_0)=0$, $\mathrm{sign}(y)$ otherwise$)$ for `ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀)`, $c=P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s$, and for a $2\times2$ real matrix $h$
--   $$T(h,s)=\int_{\mathbb R} Wr(\mathrm{par}_0,\mathrm{default})(t)\; D.W\big(\mathrm{diag}(at,1)\,h\big)\;|t|^{\,s-1/2}\;t^{-2}\,dt .$$
--   Then the integral over $e\in\mathbb R^{2\times2}$ with respect to Lebesgue measure
--   $$\int \chi(\det e)\,|\det e|^{-2}\;T(e^{-1},s)\cdot\Big(\int_{0}^{\infty} y^{\,c}\;\mathrm{godementInner3}\big(\psi_\infty\!\cdot\!\chi_y,\;S,\;e,\;1\big)\,dy\Big)\,de,$$
--   in which $\psi_\infty\!\cdot\!\chi_y$ is the shift of $\psi_\infty$ by the infinite adele with every component $y$ and $\mathrm{godementInner3}(\psi,S,h,1)=\int_{v\in\mathbb R^2} S\big(h\cdot[\,\text{rows } b\mapsto \mathbf 1_{0b}+v_0\mathbf 1_{2b},\ b\mapsto \mathbf 1_{1b}+v_1\mathbf 1_{2b}\,]\big)\,\psi(-v_1)\,dv$, equals the integral over $(x,y_1,y_2,\theta)$ in $\mathbb R\times\mathbb R\times(0,\infty)\times(0,2\pi]$ of
--   $$\chi\big((y_1y_2)^{-1}\big)\,\big|(y_1y_2)^{-1}\big|^{-2}\cdot T(g,s)\cdot \mathcal M\cdot y_2^{2}\,|y_1y_2|^{-4},$$
--   where
--   $$g=\begin{pmatrix} y_1\cos\theta+xy_2\sin\theta & -y_1\sin\theta+xy_2\cos\theta\\ y_2\sin\theta & y_2\cos\theta\end{pmatrix}$$
--   and
--   $$\mathcal M=(y_1y_2)^{-\delta}\Big((\cos\theta+i\sin\theta)\big(\tfrac1{y_1}-\tfrac1{y_2}+i\tfrac{x}{y_1}\big)\Big)^{m} e^{-\pi\left(\frac{1+x^2}{y_1^2}+\frac1{y_2^2}\right)}\,|y_1y_2|\,(-ia)^{n}\big(y_2\sin\theta+\varepsilon' i\,y_2\cos\theta\big)^{n}\cdot\tfrac12\big(\pi a^2((y_2\sin\theta)^2+(y_2\cos\theta)^2)\big)^{-\frac{c+n+1}{2}}\,\Gamma\!\Big(\tfrac{c+n+1}{2}\Big).$$
--   Thus the left-hand side is rewritten in Iwasawa coordinates — the matrix substituted for $e$ has determinant $(y_1y_2)^{-1}$ and inverse $g$, and $y_2^{2}|y_1y_2|^{-4}$ is the Jacobian factor — while the inner integral over $y\in(0,\infty)$ has been evaluated in closed form as the displayed product of a power and a value of $\Gamma$. No integrability assertion is part of the conclusion, which is the equality of the two integrals for $\mathrm{Re}\,s>\sigma_1$.
--
--   This is the archimedean step of the cubic Rankin–Selberg computation in the converse-theorem input to Langlands–Tunnell: the unfolded torus integral against the conjugate block-harmonic, column-harmonic Gaussian section on $2\times3$ matrices is put into explicit Iwasawa coordinates, the Godement inner integral over the positive reals being replaced by its Tate-type closed form with a $\Gamma$-value. It is used by the three downstream evaluations of the unfolded torus pair for the discrete-series and weight-one profiles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_conjBlockHarmonic_colHarmonic_gaussian3.lean

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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_conjBlockHarmonic_colHarmonic_gaussian3
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
    (par₀ : ZMod 2) (m n δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (ε' : ℝ) (hε' : ε' = 1 ∨ ε' = -1)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M) :
    ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
      (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
        = ∫ p : ℝ × ℝ × ℝ × ℝ in Set.univ ×ˢ (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi))),
            (let x : ℝ := p.1
             let y₁ : ℝ := p.2.1
             let y₂ : ℝ := p.2.2.1
             let θ : ℝ := p.2.2.2
             let g : Matrix (Fin 2) (Fin 2) ℝ :=
               !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
                  y₂ * Real.sin θ, y₂ * Real.cos θ]
             ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (y₁ * y₂)⁻¹ *
                 (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
               ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * g) *
                   (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                (((((y₁ * y₂)⁻¹ : ℝ) : ℂ)) ^ δ *
                  ((((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) *
                      ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ)))) ^ m *
                  (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
                  ((|y₁ * y₂| : ℝ) : ℂ) *
                  (-Complex.I * (a : ℂ)) ^ n *
                  (((y₂ * Real.sin θ : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) ^ n *
                  ((1 / 2 : ℂ) *
                    ((Real.pi * (a : ℝ) ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2) : ℝ) : ℂ)
                        ^ (-((P.centralExponent + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                    Complex.Gamma ((P.centralExponent + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
               ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) := by sorry
