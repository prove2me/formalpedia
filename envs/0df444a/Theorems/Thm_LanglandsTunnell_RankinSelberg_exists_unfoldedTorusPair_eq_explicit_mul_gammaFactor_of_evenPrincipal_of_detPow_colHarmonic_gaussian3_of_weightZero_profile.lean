-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightZero_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightZero_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/d9eee444-5d6a-519a-b571-3f5b04010706
-- title:
--   Unfolded archimedean torus pair in the weight-zero Levi branch
-- statement:
--   The setting is the archimedean Rankin–Selberg computation attached to a cubic field and an idele class character on it, in the branch where the $\mathrm{GL}_2$-parameter is of even principal type and the companion archimedean datum has weight $0$.
--
--   **Global data.** $K$ is a number field with $[K:\mathbb{Q}]=3$ (hypothesis `_hdeg`), equipped with an integral algebra structure of $\mathcal{O}_\mathbb{Q}$ on $\mathcal{O}_K$, and $\mu\colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ is an admissible twist, i.e. (by `IsAdmissibleTwist`) a continuous unitary character trivial on the principal ideles $K^\times$. The hypothesis `_hns` asserts that $\mu$ is not a base change: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose contraction $\mathfrak{p}=\mathfrak{P}\cap\mathcal{O}_\mathbb{Q}$ is a place where $\eta$ is unramified, $\mu$ of the uniformizer idele at $\mathfrak{P}$ equals $\eta$ of the uniformizer idele at $\mathfrak{p}$ raised to the inertia degree $f(\mathfrak{P}/\mathfrak{p})$.
--
--   **Archimedean components of $\mu$.** Data $u_R(w)\in\mathbb{C}$, $a_R(w)\in\mathbb{Z}/2$ for real places $w$ of $K$ and $u_C(w)\in\mathbb{C}$, $k_C(w)\in\mathbb{Z}$ for complex places, subject to `huR` and `huC`: the local component of $\mu$ at $w$ is $x\mapsto \|x\|^{\,\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$ in the sense of `IsArchCompAt`, with $(u,a)=(u_R(w),(a_R(w)).\mathrm{val})$ at real places and $(u_C(w),k_C(w))$ at complex places.
--
--   **The induced character $\omega$ on $\mathbb{Q}$.** $\omega\colon(\mathbb{A}_\mathbb{Q})^\times\to\mathbb{C}^\times$ satisfies the three clauses of `hω`: (i) $\omega$ is an admissible twist of $\mathbb{Q}$; (ii) at every finite place $p$ that is not bad for $(K,\mu)$ — not ramified in $K$ and carrying no prime above it at which $\mu$ ramifies — $\omega$ is unramified and its Euler coefficient $\omega(\text{uniformizer idele at }p)$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, minus the degree-$3$ coefficient of the induced Euler polynomial formed from the unramified coefficients $\mathfrak{P}\mapsto\mu(\text{uniformizer idele at }\mathfrak{P})$; (iii) for any data $u_R,a_R,u_C,k_C$ satisfying the same two `IsArchCompAt` conditions, at each real place $v$ of $\mathbb{Q}$ the archimedean component of $\omega$ has exponent $\sum_{w\ \mathrm{real}}u_R(w)+\sum_{w\ \mathrm{complex}}2u_C(w)$ and integer parameter $\sum_{w\ \mathrm{real}}(a_R(w)).\mathrm{val}+\sum_{w\ \mathrm{complex}}(k_C(w)+1)$ (the sums being finsums).
--
--   **Adelic and measure-theoretic bookkeeping.** $E$ is a monoid homomorphism from $(\mathbb{A}_{\mathbb{Q},\infty})^\times$ to $(\mathbb{A}_\mathbb{Q})^\times$ splitting the infinite part: by `hE`, $E(u)$ has infinite part $u$ and finite part $1$. A rational number $a\neq 0$ with $a=-1$ is given, together with a unit $a_\infty$ of the infinite adele ring whose underlying element is the image of $a$, and an additive character $\psi_\infty$ on $\mathbb{A}_{\mathbb{Q},\infty}$ with $\psi_\infty(x)=\mathrm{psiArch}(a\,x)$ for the standard archimedean character. Measurable and Borel structures on $\mathbb{A}_{\mathbb{Q},\infty}$ and on its unit group are fixed; $\nu_{\mathrm{add}}$ is the measure $\mathrm{ofReal}(|a|^{1/2})$ times the push-forward of Lebesgue measure on the mixed space along the inverse of `InfiniteAdeleRing.ringEquiv_mixedSpace ℚ`, and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb{A}_{\mathbb{Q},\infty})^\times$.
--
--   **The $\mathrm{GL}_2$-parameter over $\mathbb{Q}$ and its Whittaker data.** $P$ is a `RealArchParam` (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$ with $k\ge 1$), subject to `_hP₁`: in the principal case $|\mathrm{Re}(u_1-u_2)|<1$. Parity-indexed data are given: weights $k_w\colon \mathbb{Z}/2\times\mathrm{InfinitePlace}(\mathbb{Q})\to\mathbb{Z}$, torus profiles $W_r(\mathrm{par},w)\colon\mathbb{R}\to\mathbb{C}$, and functions $W_A(\mathrm{par})\colon \mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$. Their laws are: `hkw1`, in the principal case $(k_w(\mathrm{par},w))_\mathbb{C}=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ with $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$; `hkw2`, in the discrete case $k_w(\mathrm{par},w)=n+1$; `hWr1`, when $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$, $W_r(\mathrm{par},w)(-t)=(-1)^{a_1.\mathrm{val}}W_r(\mathrm{par},w)(t)$; `hWr2`, in the discrete case $W_r(\mathrm{par},w)$ vanishes on the negative reals; `hWr3`, when $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin integral of $t\mapsto (W_r(\mathrm{par},w)(t)+(-1)^{a_1.\mathrm{val}}W_r(\mathrm{par},w)(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}\cdot(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$; `hWr4`, for every $b'$ equal to $\mathrm{par}$ or to $\mathrm{par}+P.\mathrm{centralSign}$ the analogous Mellin transform with $(-1)^{b'.\mathrm{val}}$ equals $(P.\mathrm{twist}\,0\,b').\mathrm{archFactor}(s)$ on a right half-plane. For $W_A$: `hWAN` left equivariance under unipotents, $W_A(\mathrm{par})(u(x)h)=e^{-2\pi i a x}W_A(\mathrm{par})(h)$; `hWAZ` the central law $W_A(\mathrm{par})(z\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}W_A(\mathrm{par})(h)$ for scalar matrices; `hWAK` right equivariance $W_A(\mathrm{par})(h\kappa)=\mathrm{archWeightChar}_\mathbb{R}(k_w(\mathrm{par},\mathrm{default}))(\kappa)\,W_A(\mathrm{par})(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt` the restriction to the torus, $W_A(\mathrm{par})(\mathrm{diag}(t,1))=W_r(\mathrm{par},\mathrm{default})(t)$; and `hWAc` continuity of each $W_A(\mathrm{par})$. Finally $w_{0R}\in\mathrm{GL}_2(\mathbb{R})$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **The companion (Levi) datum.** $w_0$ is a real place of $K$, and $P_2$ is a `RealArchParam` satisfying `hP₂`: either $K$ has three real places $w_0,w_1,w_2$, pairwise distinct and exhausting the infinite places, and $P_2=\mathrm{principal}(u_R(w_1),a_R(w_1),u_R(w_2),a_R(w_2))$; or $K$ has exactly the places $w_0$ and one complex place $w_C$, and either $k_C(w_C)\neq 0$ and $P_2=\mathrm{discrete}(u_C(w_C),|k_C(w_C)|)$, or $k_C(w_C)=0$ and $P_2=\mathrm{principal}(u_C(w_C),0,u_C(w_C),1)$. $D$ is an `ArchDatumR P₂`, that is a Whittaker-type function $D.W$ on $2\times 2$ real matrices, smooth on the invertible locus, with the unipotent law, the central law governed by $P_2$, and an entire zeta function satisfying the functional equation with $\epsilon$-factor of $P_2$, finite order, and the prescribed decay bounds. An integer $k_0$ is given with `hDW`: $D.W(x\kappa)=\mathrm{archWeightChar}_\mathbb{R}(k_0)(\kappa)\,D.W(x)$ for $\kappa\in$ `rowIsometrySubgroup₀ ℝ`. Further, `hDE` asserts that $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x\ne 0$; `hDnz` asserts $D.W$ is not identically zero; and `hk₀min` asserts minimality of $k_0$: in the principal case $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, in the discrete case $k_0=m+1$.
--
--   **Even principal frame and section.** Complex numbers $\nu_1,\nu_2$ and $b\in\mathbb{Z}/2$ with `hPev`: $P=\mathrm{principal}(\nu_1,b,\nu_2,b)$. The hypothesis `hLevi` requires that if $k_0=0$ then every principal presentation of $P_2$ has first sign $a_1=b$. A natural number $n$ with $(n:\mathbb{Z})=k_0$, and $\delta\in\{0,1\}$ with $\delta\equiv a_R(w_0)+b \pmod 2$, are given, and $S$ is the function on $2\times 3$ real matrices
--   $$S(M)=(M_{00}M_{11}-M_{01}M_{10})^{\delta}\,(M_{02}-iM_{12})^{n}\,\exp\Big(-\pi\sum_{i,j}M_{ij}^2\Big).$$
--
--   **The weight-zero branch.** Complex numbers $u_1,u_2$ with $P_2=\mathrm{principal}(u_1,b,u_2,b)$ and $k_0=0$, and $\rho\in\mathbb{C}$ such that for every $\tau>0$
--   $$D.W\big(\mathrm{diag}(\tau,1)\big)=\rho\,\tau\cdot 4\int_{0}^{\infty} r^{u_1}e^{-\pi r^2}\,(\tau/r)^{u_2}e^{-\pi(\tau/r)^2}\,\frac{dr}{r}.$$
--
--   **Conclusion.** There exists $\sigma_a\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\mathrm{Re}\,s>\sigma_a$ the integral over $e\in\mathbb{R}^{2\times 2}$ of
--   $$\mathrm{quasiChar}(u_R(w_0)+2,\;a_R(w_0))(\det e)\cdot |\det e|^{-2}\cdot T(e,s)\cdot M(e,s)$$
--   equals $\big((-1)^{b.\mathrm{val}}\pi\big)\rho$ times the product of $\Gamma_\mathbb{R}(s+\tfrac12+x)$ over the multiset `twistedGammaR K (archOfParamR K P) uR aR` and the product of $\Gamma_\mathbb{C}(s+\tfrac12+x)$ over the multiset `twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC`; here $\mathrm{quasiChar}(u,a)(y)=|y|^{u}$ times $1$ if $a=0$ and $\mathrm{sign}(y)$ otherwise, and the two multisets are the sums over the real places of the $\Gamma_\mathbb{R}$- resp. $\Gamma_\mathbb{C}$-shifts of $P.\mathrm{twist}(u_R(w),a_R(w))$ together with, for the complex places, the $\Gamma_\mathbb{C}$-shifts of the base change of $P$ twisted by $(u_C(w),k_C(w))$.
--
--   The two inner factors are the torus transform
--   $$T(e,s)=\int_{\mathbb{R}} W_r(b,\mathrm{default})(t)\,D.W\big(\mathrm{diag}(at,1)\,e^{-1}\big)\,|t|^{s-1/2}\,t^{-2}\,dt$$
--   and the Godement–Tate transform of the section,
--   $$M(e,s)=\int_{0}^{\infty} y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\;\mathrm{godementInner3}\big(\psi_\infty\text{ shifted by }\mathrm{ofReal}(y),\,S,\,e,\,1\big)\,dy,$$
--   where $\mathrm{godementInner3}(\psi,S,h,m)=\int_{v\in\mathbb{R}^2}S\big(h\cdot(\text{rows } m_{0\bullet}+v_0m_{2\bullet},\,m_{1\bullet}+v_1m_{2\bullet})\big)\,\psi(\mathrm{ofReal}(-v_1))\,dv$, taken at $m=1$, and $\mathrm{default}$ denotes the distinguished infinite place of $\mathbb{Q}$.
--
--   This is the archimedean half of the Rankin–Selberg unfolding used in the converse-theorem step of the Langlands–Tunnell argument for a cubic field: it evaluates the unfolded archimedean torus-pair integral of the determinant-power, column-harmonic Gaussian section against the companion Whittaker datum, in the branch where the parameter is even principal and the companion datum has weight $k_0=0$, producing the expected product of $\Gamma_\mathbb{R}$- and $\Gamma_\mathbb{C}$-factors with the explicit constant $(-1)^{b}\pi\rho$. It feeds the statement combining this primal evaluation with its dual counterpart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightZero_profile.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightZero_profile
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

    (u₁ u₂ : ℂ) (hP₂eq : P₂ = RealArchParam.principal u₁ b u₂ b) (hk₀ : k₀ = 0)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((τ) / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * ((τ) / r) ^ 2)) : ℂ)) / (r : ℂ))) :
    ∃ σa : ℝ, (∀ s : ℂ, σa < s.re →
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr b default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
              = (((-1 : ℂ) ^ b.val * (Real.pi : ℂ)) * ρ) * (((twistedGammaR K (archOfParamR K P) uR aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) := by sorry
