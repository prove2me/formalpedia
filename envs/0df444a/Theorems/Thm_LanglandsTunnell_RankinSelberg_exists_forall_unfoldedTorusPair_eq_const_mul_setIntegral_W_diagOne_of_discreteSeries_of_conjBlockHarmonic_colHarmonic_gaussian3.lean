-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/0399e2e2-2b16-527b-8a36-bbb4fa363b6a
-- title:
--   Unfolded torus pair for a discrete-series GL₂ profile
-- statement:
--   Throughout, $K$ is a number field whose ring of integers is an integral $\mathcal O_{\mathbb Q}$-algebra, and $\mu\colon(\mathbb A_K)^\times\to\mathbb C^\times$ is a character of the ideles of $K$.
--
--   **Arithmetic frame.** The hypothesis `_hdeg` asserts $[K:\mathbb Q]=3$. The hypothesis `_hμ` asserts that $\mu$ is an admissible twist, i.e. trivial on the principal ideles coming from $K^\times$, continuous, and unitary ($|\mu(x)|=1$ for all $x$). The hypothesis `_hns` asserts that $\mu$ does not descend: there is no admissible twist $\eta$ of $\mathbb Q$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and whose restriction $\mathfrak p=\mathfrak P\cap\mathcal O_{\mathbb Q}$ is a place where $\eta$ is unramified, $\mu$ of the uniformiser idele at $\mathfrak P$ equals $\eta$ of the uniformiser idele at $\mathfrak p$ raised to the inertia degree `inertiaDeg'` of $\mathfrak P$ over $\mathfrak p$. (Here unramifiedness of a character at a finite place means that its local component is trivial on the units of the local integers.)
--
--   **Archimedean components of $\mu$.** Families $uR,aR$ (indexed by the real places of $K$, with values in $\mathbb C$ and $\mathbb Z/2$) and $uC,kC$ (indexed by the complex places, with values in $\mathbb C$ and $\mathbb Z$) are given; `huR` and `huC` assert `IsArchCompAt`, namely that at each real place $w$ the archimedean local component of $\mu$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,uR(w)}\,(x/\|x\|)^{(aR(w)).\mathrm{val}}$, and similarly at each complex place $w$ with exponents $uC(w)$ and $kC(w)$.
--
--   **The descended character $\omega$ of $\mathbb Q$.** A character $\omega\colon(\mathbb A_{\mathbb Q})^\times\to\mathbb C^\times$ is given, and `hω` has three clauses: $\omega$ is an admissible twist; for every finite place $p$ of $\mathbb Q$ which is not a bad place for $(K,\mu)$ — that is, no prime above $p$ has ramification index $\neq 1$ and $\mu$ is unramified at every prime above $p$ — the character $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\text{uniformiser idele at }p)$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, i.e. minus the degree-$3$ coefficient of the induced Euler polynomial `inducedEulerPoly` formed from the coefficients $\mathfrak P\mapsto\mu(\text{uniformiser at }\mathfrak P)$ (set to $0$ at ramified $\mathfrak P$); and, for every family $(uR,aR,uC,kC)$ satisfying the same two archimedean-component conditions and every real place $v$ of $\mathbb Q$, the archimedean component of $\omega$ at $v$ has exponent $\sum^{f}_{w\ \mathrm{real}}uR(w)+\sum^{f}_{w\ \mathrm{complex}}2\,uC(w)$ and integer parameter $\sum^{f}_{w\ \mathrm{real}}(aR(w)).\mathrm{val}+\sum^{f}_{w\ \mathrm{complex}}(kC(w)+1)$, the sums being finite sums over the infinite places of $K$.
--
--   **Adelic normalisations.** A homomorphism $E\colon(\mathbb A_{\mathbb Q,\infty})^\times\to(\mathbb A_{\mathbb Q})^\times$ with `hE`: the infinite part of $E(u)$ is $u$ and the finite part is $1$. A rational number $a$ with $a\neq 0$ and $a=-1$, a unit $a_\infty$ of the infinite adele ring whose underlying element is the image of $a$, and an additive character $\psi_\infty$ of $\mathbb A_{\mathbb Q,\infty}$ with $\psi_\infty(x)=\psi_{\mathrm{arch}}(a\,x)$ for the standard archimedean character `psiArch`. Measurable-space and Borel structures on $\mathbb A_{\mathbb Q,\infty}$ and on its units are assumed, together with a measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the pushforward of Lebesgue measure on the mixed space along the inverse of `InfiniteAdeleRing.ringEquiv_mixedSpace ℚ`, and a Haar measure $\nu_{\mathrm{mul}}$ on $(\mathbb A_{\mathbb Q,\infty})^\times$.
--
--   **The $GL_2$ archimedean parameter and its Whittaker package.** $P$ is a real archimedean parameter (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb C$, $a_i\in\mathbb Z/2$, or $\mathrm{discrete}(u,k)$ with $k\ge 1$), and `_hP₁` requires $|\mathrm{Re}(u_1-u_2)|<1$ whenever $P$ is principal. Data $kw\colon\mathbb Z/2\times\{\text{real places of }\mathbb Q\}\to\mathbb Z$, $W_r\colon \mathbb Z/2\times\{\text{places}\}\times\mathbb R\to\mathbb C$ and $W_A\colon\mathbb Z/2\times GL_2(\mathbb R)\to\mathbb C$ are given, subject to: `hkw1`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $kw(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ (with $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$); `hkw2`, if $P=\mathrm{discrete}(u_0,n)$ then $kw(\mathrm{par},w)=n+1$; `hWr1`, in the principal case with equal signs $a_1=a_2$ and $\mathrm{par}=a_1$, the parity law $W_r(\mathrm{par},w,-t)=(-1)^{a_1.\mathrm{val}}W_r(\mathrm{par},w,t)$; `hWr2`, in the discrete case $W_r(\mathrm{par},w,t)=0$ for $t<0$; `hWr3`, in the principal case with $a_1=a_2$ and $\mathrm{par}=a_1+1$, existence of $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (W_r(\mathrm{par},w,t)+(-1)^{a_1.\mathrm{val}}W_r(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$ at $s$; `hWr4`, for every $\mathrm{par}$ and every $b$ with $b=\mathrm{par}$ or $b=\mathrm{par}+P.\mathrm{centralSign}$, existence of $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (W_r(\mathrm{par},w,t)+(-1)^{b.\mathrm{val}}W_r(\mathrm{par},w,-t))/t$ converges and equals the archimedean factor of $P.\mathrm{twist}\,0\,b$ at $s$; `hWAN`, $W_A(\mathrm{par},\,\mathrm{unipotentGL2}(x)\,h)=e^{-2\pi i a x}W_A(\mathrm{par},h)$; `hWAZ`, the central law $W_A(\mathrm{par},z\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}W_A(\mathrm{par},h)$ for scalar $z\in\mathbb R^\times$; `hWAK`, the right weight law $W_A(\mathrm{par},h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(kw(\mathrm{par},\mathrm{default}))(\kappa)\,W_A(\mathrm{par},h)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hWAt`, $W_A(\mathrm{par},\mathrm{diagOne}(t))=W_r(\mathrm{par},\mathrm{default},t)$ for $t\in\mathbb R^\times$; and `hWAc`, continuity of each $W_A(\mathrm{par},\cdot)$. Finally $w_{0R}\in GL_2(\mathbb R)$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **The Levi datum.** $w_0$ is a real place of $K$, and $P_2$ is a real archimedean parameter subject to `hP₂`: either $K$ has exactly three real places $w_0,w_1,w_2$, pairwise distinct and exhausting the infinite places, and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$; or $K$ has a complex place $w_C$ and the infinite places are exactly $w_C$ and $w_0$, with either $kC(w_C)\neq 0$ and $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$, or $kC(w_C)=0$ and $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$. Then $D$ is an archimedean datum `ArchDatumR P₂`, that is a function $D.W$ on $2\times2$ real matrices, smooth on the invertible locus, with the unipotent law $D.W(\mathrm{unip}(x)g)=\psi(x)D.W(g)$, the central law $D.W(zg)=\mathrm{centralChar}(P_2)(z)\,|z|\,D.W(g)$ for $z\neq0$, and an accompanying entire family of completed zeta functions satisfying the integral representation by the archimedean factor of $P_2.\mathrm{twist}\,u\,a$, the local functional equation with epsilon factor, finite-order growth in vertical strips and the prescribed decay bounds at $|y|\ge1$ and $0<|y|\le1$. An integer $k_0$ is given with: `hDW`, $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for $\det x\neq0$; `hDnz`, $D.W$ is not identically zero on $GL_2(\mathbb R)$; and `hk₀min`, if $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, while if $P_2=\mathrm{discrete}(u,m')$ then $k_0=m'+1$.
--
--   **Discrete-series profile and flat section.** The parameter $P$ is discrete: $P=\mathrm{discrete}(u_P,n_P)$ with $n_P\ge1$, and $m=n_P+1$. A natural number $n$ and a sign $\varepsilon'\in\mathbb R$ satisfy the column-matching hypothesis `hcol`: either $\varepsilon'=-1$ and $n=k_0-m$, or $\varepsilon'=1$ and $n=m-k_0$. A parity $\mathrm{par}_0\in\mathbb Z/2$ is fixed. The Schwartz section $S$ on $2\times3$ real matrices is given by
--   $$S(M)=\big((M_{00}-iM_{10})-i(M_{01}-iM_{11})\big)^m\,\big(M_{02}+\varepsilon' i M_{12}\big)^n\,e^{-\pi\sum_{i,b}M_{ib}^2}.$$
--   Finally the profile of the $GL_2$ Whittaker function in the fixed parity is explicit: $W_r(\mathrm{par}_0,\mathrm{default},t)=2\,t^{\,u_P+n_P/2+1}e^{-2\pi t}$ for $t>0$ (`hWpos`) and $W_r(\mathrm{par}_0,\mathrm{default},t)=0$ for $t<0$ (`hWneg`).
--
--   **Conclusion.** There exists $\sigma_a\in\mathbb R$ such that for every $s\in\mathbb C$ with $\mathrm{Re}\,s>\sigma_a$,
--   $$\int_{e}\mathrm{quasiChar}(uR(w_0)+2,\,aR(w_0))(\det e)\;|\det e|^{-2}\;I_1(e,s)\,I_2(e,s)\,de$$
--   equals
--   $$\pi\,\Gamma_{\mathbb R}\!\big(P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s+n+1\big)\,(-\varepsilon')^{n}\,(-1)^{(aR(w_0)).\mathrm{val}+m}\,2^{m}\,(2\pi)^{-(s+u_P+uR(w_0)+m/2)}\,\Gamma\!\big(s+u_P+uR(w_0)+\tfrac m2\big)\int_{0}^{\infty}D.W(\mathrm{diagOne}(v))\,v^{\,s+u_P+m/2-2}\,e^{-2\pi v}\,dv.$$
--   Here the outer integral is over $e\in\mathbb R^{2\times 2}$ for Lebesgue measure on the four entries; $\mathrm{quasiChar}(u,\alpha)(y)=|y|^{u}$ if $\alpha=0$ and $|y|^{u}\,\mathrm{sign}(y)$ otherwise; and
--   $$I_1(e,s)=\int_{\mathbb R}W_r(\mathrm{par}_0,\mathrm{default},t)\;D.W\!\big(\mathrm{diagOne}(a\,t)\,e^{-1}\big)\;|t|^{\,s-1/2}\;t^{-2}\,dt,$$
--   $$I_2(e,s)=\int_{0}^{\infty}y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\;\mathrm{godementInner3}\big(\psi_\infty\!\cdot\!(\mathrm{ofReal}\,y),\,S,\,e,\,1\big)\,dy,$$
--   where $\mathrm{diagOne}(y)=\begin{pmatrix}y&0\\0&1\end{pmatrix}$, the character in $I_2$ is the multiplicative shift of $\psi_\infty$ by the infinite adele $\mathrm{ofReal}\,y$ with all coordinates $y$, and
--   $$\mathrm{godementInner3}(\psi,S,e,1)=\int_{v\in\mathbb R^2}S\!\left(e\cdot\begin{pmatrix}1&0&v_0\\0&1&v_1\end{pmatrix}\right)\psi\big(\mathrm{ofReal}(-v_1)\big)\,dv,$$
--   the $2\times3$ matrix being the one obtained from the identity $3\times3$ matrix by the prescription in `godementInner3` with $m=1$. The functions $\Gamma_{\mathbb R}$ and $\Gamma$ are `Complex.Gammaℝ` and `Complex.Gamma`.
--
--   This is the archimedean Rankin–Selberg computation at the distinguished real place $w_0$ in the $GL_3\times GL_2$ setting attached to a cubic field and a non-descending idele class character: for a discrete-series $GL_2$ profile and the degree-$m$ flat Schwartz section, the unfolded torus pair is evaluated in closed form as a product of $\Gamma$-factors times the Laplace–Mellin transform $\int_0^\infty D.W(\mathrm{diag}(v,1))v^{s+u_P+m/2-2}e^{-2\pi v}\,dv$ of the positive torus sheet of the Levi datum, with no hypotheses on $D$ beyond its unipotent, central, weight and Casimir laws. It is the common core of the three branch statements (weight-zero, weight-one and discrete Levi) that cite it, each of which finishes by evaluating that Laplace–Mellin transform for its explicit sheet.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
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
    (uP : ℂ) (nP : ℕ) (hnP : 1 ≤ nP) (hPdisc : P = RealArchParam.discrete uP nP hnP)
    (m : ℕ) (hm : m = nP + 1)
    (n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (hWpos : ∀ t : ℝ, 0 < t → Wr par₀ default t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → Wr par₀ default t = 0) :
    ∃ σa : ℝ, ∀ s : ℂ, σa < s.re →
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
              = (Real.pi : ℂ) * Complex.Gammaℝ (P.centralExponent + P₂.centralExponent + 2 * s + (n : ℂ) + 1) *
              ((-(ε' : ℂ)) ^ n) * (-1 : ℂ) ^ ((aR w₀ h₀).val + m) * (2 : ℂ) ^ m *
              (2 * (Real.pi : ℂ)) ^ (-(s + uP + uR w₀ h₀ + (m : ℂ) / 2)) * Complex.Gamma (s + uP + uR w₀ h₀ + (m : ℂ) / 2) *
              (∫ v in Set.Ioi (0 : ℝ), D.W (ArchR.diagOne v) * ((v : ℝ) : ℂ) ^ (s + uP + (m : ℂ) / 2 - 2) *
                (Real.exp (-(2 * Real.pi * v)) : ℂ)) := by sorry
