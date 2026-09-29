-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_setIntegral_dualConfig_of_evenPrincipal_of_detPow_colHarmonic_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_evenPrincipal_of_detPow_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/bbffc300-e8d3-58f4-bef7-417a2a3a7b30
-- title:
--   Dual unfolding of the even-type archimedean torus pair
-- statement:
--   The setting is the archimedean frame of the cubic induction for a cubic field.
--
--   **The cubic field and its idele class character.** $K$ is a number field equipped with an integral algebra structure $\mathcal O_{\mathbb Q}\to\mathcal O_K$, and `_hdeg` asserts $[K:\mathbb Q]=3$. A character $\mu\colon(\mathbb A_K)^\times\to\mathbb C^\times$ is given, and `_hμ` asserts that $\mu$ is an admissible twist, i.e. it is trivial on the principal ideles $K^\times$, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` asserts that $\mu$ does not come from $\mathbb Q$ in the following sense: there is no admissible twist $\eta$ of $\mathbb Q$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and whose underlying prime $p=\mathfrak P\cap\mathcal O_{\mathbb Q}$ is unramified for $\eta$, one has $\mu(\varpi_{\mathfrak P})=\eta(\varpi_{p})^{f(\mathfrak P/p)}$, where $\varpi$ denotes the uniformizer idele and $f$ the residue degree `inertiaDeg'`. The archimedean behaviour of $\mu$ is recorded by data $u_R(w)\in\mathbb C$, $a_R(w)\in\mathbb Z/2$ for each real place $w$ of $K$ and $u_C(w)\in\mathbb C$, $k_C(w)\in\mathbb Z$ for each complex place; `huR` and `huC` assert `IsArchCompAt`, that is, at each place $w$ the local component of $\mu$ on $(K_w)^\times$ is $x\mapsto \|x\|^{\,\mathrm{mult}(w)\cdot u}\,(\iota_w(x)/\|x\|)^{m}$ with $(u,m)=(u_R(w),a_R(w)_{\mathrm{val}})$ at real places and $(u_C(w),k_C(w))$ at complex places.
--
--   **The induced character on $\mathbb Q$.** A character $\omega\colon(\mathbb A_{\mathbb Q})^\times\to\mathbb C^\times$ is given, and `hω` has three clauses: $\omega$ is an admissible twist; for every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ (that is, $p$ is neither ramified in $K$ nor twist-ramified above), $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, the negative of the degree-$3$ coefficient of the induced Euler polynomial formed from the coefficients $\mathfrak P\mapsto\mu(\varpi_{\mathfrak P})$ (taken to be $0$ at ramified $\mathfrak P$); and, for every choice of archimedean data $(u_R,a_R,u_C,k_C)$ satisfying the two `IsArchCompAt` conditions for $\mu$, the local component of $\omega$ at the real place $v$ of $\mathbb Q$ has parameters $\sum_{w\ \mathrm{real}}u_R(w)+\sum_{w\ \mathrm{complex}}2u_C(w)$ and exponent $\sum_{w\ \mathrm{real}}a_R(w)_{\mathrm{val}}+\sum_{w\ \mathrm{complex}}(k_C(w)+1)$.
--
--   **Adelic and measure-theoretic data.** A monoid homomorphism $E\colon(\mathbb A_{\mathbb Q,\infty})^\times\to(\mathbb A_{\mathbb Q})^\times$ is given with `hE`: the infinite part of $E(u)$ is $u$ and the finite part is $1$. A rational number $a$ is given with $a\neq0$ and $a=-1$, together with a unit $a_\infty$ of the infinite adele ring whose underlying element is the image of $a$. The additive character $\psi_\infty$ on $\mathbb A_{\mathbb Q,\infty}$ satisfies $\psi_\infty(x)=\psi_{\mathrm{arch}}(a\,x)$ for the standard archimedean character $\psi_{\mathrm{arch}}$. Measurable and Borel structures on $\mathbb A_{\mathbb Q,\infty}$ and on its unit group are assumed; $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the identification of $\mathbb A_{\mathbb Q,\infty}$ with the mixed space, and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb A_{\mathbb Q,\infty})^\times$.
--
--   **The $GL_2$ archimedean profile.** $P$ is a real archimedean parameter, and `_hP₁` asserts that if $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $|\mathrm{Re}(u_1-u_2)|<1$. Data $k_w\colon\mathbb Z/2\times\{\text{places of }\mathbb Q\}\to\mathbb Z$, $W_r\colon\mathbb Z/2\times\{\text{places}\}\times\mathbb C\to\mathbb C$ and $W_A\colon\mathbb Z/2\times GL_2(\mathbb R)\to\mathbb C$ are given, subject to: `hkw1`, in the principal case $k_w(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ (with $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$); `hkw2`, in the discrete case $P=\mathrm{discrete}(u_0,n,\cdot)$, $k_w(\mathrm{par},w)=n+1$; `hWr1`, in the principal case with equal parities $a_1=a_2$ and $\mathrm{par}=a_1$, the symmetry $W_r(\mathrm{par},w,-t)=(-1)^{a_{1,\mathrm{val}}}W_r(\mathrm{par},w,t)$; `hWr2`, in the discrete case $W_r(\mathrm{par},w,t)=0$ for $t<0$; `hWr3`, in the principal case with equal parities and $\mathrm{par}=a_1+1$, the existence of $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (W_r(\mathrm{par},w,t)+(-1)^{a_{1,\mathrm{val}}}W_r(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$; `hWr4`, for $b'=\mathrm{par}$ or $b'=\mathrm{par}+\mathrm{centralSign}(P)$, the analogous Mellin transform equals the archimedean factor of $P$ twisted by $(0,b')$; `hWAN`, the unipotent law $W_A(\mathrm{par},u(x)h)=e^{-2\pi i a x}W_A(\mathrm{par},h)$; `hWAZ`, the central law $W_A(\mathrm{par},z\cdot h)=|z|^{\,\mathrm{centralExponent}(P)+1}(z/|z|)^{\mathrm{centralSign}(P)_{\mathrm{val}}}W_A(\mathrm{par},h)$ for scalars $z$; `hWAK`, right equivariance $W_A(\mathrm{par},h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_w(\mathrm{par},\ast))(\kappa)\,W_A(\mathrm{par},h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, $W_A(\mathrm{par},\mathrm{diag}(t,1))=W_r(\mathrm{par},\ast,t)$ for $t\in\mathbb R^\times$; and `hWAc`, continuity of each $W_A(\mathrm{par},\cdot)$. Finally $w_{0R}\in GL_2(\mathbb R)$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **The Levi datum.** $w_0$ is a real place of $K$, and $P_2$ is a real archimedean parameter subject to `hP₂`: either $K$ has exactly three real places $w_0,w_1,w_2$, pairwise distinct and exhausting the infinite places, and $P_2=\mathrm{principal}(u_R(w_1),a_R(w_1),u_R(w_2),a_R(w_2))$; or $K$ has a complex place $w_C$ such that $w_C$ and $w_0$ exhaust the infinite places, and either $k_C(w_C)\neq0$ and $P_2=\mathrm{discrete}(u_C(w_C),|k_C(w_C)|)$, or $k_C(w_C)=0$ and $P_2=\mathrm{principal}(u_C(w_C),0,u_C(w_C),1)$. Then $D$ is a real archimedean Whittaker datum of parameter $P_2$ (a function $D.W$ on $2\times2$ real matrices, smooth on the invertible locus, with the prescribed unipotent and central laws and the zeta-integral, functional-equation, finite-order and decay package), $k_0\in\mathbb Z$, and: `hDW`, $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(D.W)(x)=\mathrm{laplaceEigenvalue}(P_2)\,D.W(x)$ for $\det x\neq0$; `hDnz`, $D.W$ does not vanish identically; `hk₀min`, in the principal case $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, and in the discrete case $P_2=\mathrm{discrete}(u,m)$ one has $k_0=m+1$.
--
--   **Even type and the section.** Complex numbers $\nu_1,\nu_2$ and $b\in\mathbb Z/2$ are given with `hPev`: $P=\mathrm{principal}(\nu_1,b,\nu_2,b)$, so that $\mathrm{centralExponent}(P)=\nu_1+\nu_2$ and $\mathrm{centralSign}(P)=0$. The hypothesis `hLevi` asserts that if $k_0=0$ and $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $a_1=b$. Natural numbers $n$ and $\delta$ satisfy $n=k_0$, $\delta\in\{0,1\}$ and $\delta\equiv a_R(w_0)+b\pmod 2$. The Schwartz section $S$ on $2\times3$ real matrices is given explicitly by
--   $$S(M)=(M_{00}M_{11}-M_{01}M_{10})^{\delta}\,(M_{02}-iM_{12})^{n}\,e^{-\pi\sum_{i,j}M_{ij}^{2}}.$$
--   Finally $s\in\mathbb C$ is arbitrary.
--
--   **Conclusion.** Write, for $a_1\neq0$ and $a_2>0$, $q=q(a_1,a_2)$ for the element `upperUnit a₁ 0 a₂` of $GL_2(\mathbb R)$, i.e. the matrix $\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$, so $|\det q|=|a_1a_2|$; write $g(q)$ for the archimedean component of the image of $q$ under transport to the completion at the unique infinite place of $\mathbb Q$ (`archRealGLAt`), inclusion into the adelic $GL_2$, and the block embedding $\iota$ into the adelic $GL_3$; write $\Phi=\mathrm{jacquetVector3}\,D\,u_R(w_0)\,a_R(w_0)\,a\,\psi_\infty\,S$ and $\mathrm{dualWhittakerFn3}\,\Phi(g)=\Phi(w_3\cdot{}^{t}g^{-1})$ with $w_3$ the $3\times3$ antidiagonal permutation matrix; and write $\chi_{u,\epsilon}(y)=|y|^{u}$ if $\epsilon=0$, $|y|^{u}\mathrm{sgn}(y)$ if $\epsilon=1$, for the real quasi-character `ArchR.quasiChar`. Then the iterated integral over $a_2\in(0,\infty)$ and $a_1\in\mathbb R$ (Lebesgue in each variable, the integrand being set to $0$ unless $a_1\neq0$ and $a_2>0$) of
--   $$\Big(|\det q|\,W_A\big(b,\;w_{0R}\cdot{}^{t}q^{-1}\big)\cdot\big(\mathrm{dualWhittakerFn3}\,\Phi\big)(g(q))\Big)\cdot|\det q|^{\,s-1/2}\cdot a_1^{-2}$$
--   equals the iterated integral, over the same domain and with the same convention, of
--   $$\Big(|a_1a_2|\cdot\Big(i^{\,k_w(b,\ast)}\,\big(|-a_1^{-1}|^{\,\mathrm{centralExponent}(P)+1}\,\big((-a_1^{-1})/|-a_1^{-1}|\big)^{\mathrm{centralSign}(P)_{\mathrm{val}}}\big)\,W_r\big(b,\ast,-a_1/a_2\big)\Big)\cdot\Big(\chi_{u_R(w_0)+1,\,a_R(w_0)}\big(-(a_1a_2)^{-1}\big)\cdot I(a_1,a_2)\Big)\cdot|a_1a_2|^{\,s-1/2}\Big)\cdot a_1^{-2},$$
--   where $\ast$ denotes the infinite place of $\mathbb Q$ and the inner factor is the integral over $e\in M_2(\mathbb R)$
--   $$I(a_1,a_2)=\int\Big[(e_{00}-ie_{10})^{n}\,e^{-\pi\left(a_2^{-2}(e_{01}^{2}+e_{11}^{2})+e_{00}^{2}+e_{10}^{2}\right)}\,\big(a_1^{2}|\det e|^{-1}\big)\,\big(-i\,a\,a_1a_2^{-1}\big(e_{11}(e^{-1})_{10}-e_{01}(e^{-1})_{11}\big)\big)^{\delta}\,e^{-\pi a^{2}a_1^{2}\left((e^{-1})_{10}^{2}+(e^{-1})_{11}^{2}\right)}\Big]\cdot\chi_{u_R(w_0)+2,\,a_R(w_0)}(\det e)\,|\det e|^{-2}\cdot D.W\big(\mathrm{diag}(a,1)\cdot e^{-1}\big)\,de.$$
--
--   This is the archimedean unfolding step of the Rankin–Selberg computation attached to the cubic induction: it rewrites the folded dual torus pairing of the $GL_2$ Whittaker profile $W_A$ against the dual Whittaker function of the Jacquet vector of the $\det^{\delta}\cdot(\text{column})^{n}$ Gaussian section over the Siegel half-torus as an explicit iterated integral in the coordinates $(a_1,a_2)$, with the inner $M_2(\mathbb R)$-integral in closed form. It feeds the three theorems which, case by case according to the shape of the Levi profile (discrete series, weight one, weight zero), evaluate this integral as the archimedean root number times an explicit factor times the gamma factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_setIntegral_dualConfig_of_evenPrincipal_of_detPow_colHarmonic_gaussian3.lean

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

theorem LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_evenPrincipal_of_detPow_colHarmonic_gaussian3
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
    (s : ℂ) :
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA b (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
      = (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                ((((|a₁ * a₂| : ℝ) : ℂ) *
                    (Complex.I ^ (kw b default) *
                      ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
                        ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) *
                      Wr b default (-a₁ / a₂))) *
                  (ArchR.quasiChar (uR w₀ h₀ + 1) (aR w₀ h₀) (-(a₁ * a₂)⁻¹) *
                    ∫ e : Fin 2 → Fin 2 → ℝ,
                      ((((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ n *
                    (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
                    (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
                    ((-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((e 1 1 : ℝ) : ℂ) * (((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) - ((e 0 1 : ℝ) : ℂ) * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)))) ^ δ) *
                    (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
                        (ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) *
                        D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹)) *
                  (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0) := by sorry
