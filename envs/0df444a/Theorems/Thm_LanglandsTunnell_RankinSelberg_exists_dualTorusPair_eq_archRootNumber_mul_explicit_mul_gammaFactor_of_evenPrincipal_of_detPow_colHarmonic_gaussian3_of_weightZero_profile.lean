-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightZero_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightZero_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/cc10ec2f-fa6e-5355-8bc9-a7625657773c
-- title:
--   Dual torus pair, even principal type, weight-zero Levi branch
-- statement:
--   The setting is a number field $K$ of degree $3$ over $\mathbb{Q}$ (hypothesis `_hdeg`), with $\mathcal{O}_{\mathbb{Q}}$ acting integrally on $\mathcal{O}_K$, together with a character $\mu$ of the idele units of $K$ with values in $\mathbb{C}^\times$ subject to `_hμ`, i.e. $\mu$ is trivial on the principal ideles $K^\times$, continuous and unitary. The hypothesis `_hns` asserts that $\mu$ is not obtained from $\mathbb{Q}$: there is no character $\eta$ of the ideles of $\mathbb{Q}$, trivial on $\mathbb{Q}^\times$, continuous and unitary, such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and with $\eta$ unramified at the prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ below it, $\mu$ of a uniformizer idele at $\mathfrak{P}$ equals $\eta$ of a uniformizer idele at $p$ raised to the inertia degree of $\mathfrak{P}$ over $p$.
--
--   The archimedean type of $\mu$ is recorded by families $uR, aR$ indexed by the real places and $uC, kC$ indexed by the complex places: `huR` says that at each real place $w$ the local component of $\mu$ on $(K_w)^\times$ is $x \mapsto \|x\|^{\mathrm{mult}(w)\,uR(w)}\,(x/\|x\|)^{aR(w)}$ (the exponent being the representative of $aR(w) \in \mathbb{Z}/2$), and `huC` says the same at each complex place with exponents $uC(w)$ and $kC(w) \in \mathbb{Z}$.
--
--   A character $\omega$ of the ideles of $\mathbb{Q}$ is given, with `hω` in three clauses: $\omega$ is trivial on $\mathbb{Q}^\times$, continuous and unitary; at every prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ which is neither ramified in $K$ nor twist-ramified above for $\mu$, $\omega$ is unramified and its Euler coefficient at $p$ equals $-1$ times the degree-$3$ coefficient of the induced Euler polynomial formed from the unramified coefficients of $\mu$; and, for every family $(uR,aR,uC,kC)$ satisfying the two archimedean compatibilities above, the component of $\omega$ at the real place of $\mathbb{Q}$ has exponent $\sum_w uR(w) + \sum_w 2\,uC(w)$ and sign exponent $\sum_w aR(w) + \sum_w (kC(w)+1)$, the sums being over the real and the complex places of $K$ respectively.
--
--   The remaining global data are: a homomorphism $E$ from the units of the infinite adele ring of $\mathbb{Q}$ to the ideles, splitting the infinite part and with trivial finite part (`hE`); a rational $a \neq 0$ with $a = -1$ (`ha`, `ha1`); an infinite-adelic unit $aInf$ whose underlying element is the image of $a$ (`haInf`); the additive character $\psi_\infty$ of the infinite adele ring given by $x \mapsto \psi_{\mathrm{arch}}(a x)$ (`hpsiInf`); an additive measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the transport of Lebesgue measure along the inverse of the identification of the infinite adele ring with its mixed space (`hν_add`); and a Haar measure $\nu_{\mathrm{mul}}$ on the units, together with the measurability and Borel instances for the infinite adele ring and its unit group.
--
--   The archimedean parameter $P$ of the $\mathrm{GL}_2/\mathbb{Q}$ side is constrained by `_hP₁` (in the principal case the real parts of the two exponents differ by less than $1$) and, by `hPev`, is of even principal type: $P = \mathrm{principal}\,\nu_1\,b\,\nu_2\,b$ for complex $\nu_1,\nu_2$ and a single parity $b \in \mathbb{Z}/2$. Attached to $P$ are a weight function $kw$, a family of functions $Wr$ on $\mathbb{R}$ and a family of functions $WA$ on $\mathrm{GL}_2(\mathbb{R})$, all indexed by a parity sheet $par \in \mathbb{Z}/2$, subject to the following groups of hypotheses, each stated for every $par$. Weights: `hkw1`, in the principal case $kw(par,w) = \mathrm{signShift}(a_1+par)+\mathrm{signShift}(a_2+par)$, and `hkw2`, in the discrete case of length $n$, $kw(par,w) = n+1$. Torus profiles: `hWr1`, in the equal-parity principal case with $par = a_1$, $Wr(par,w)(-t) = (-1)^{a_1} Wr(par,w)(t)$; `hWr2`, in the discrete case $Wr(par,w)$ vanishes on the negative axis; `hWr3`, in the equal-parity principal case with $par = a_1+1$, the Mellin transform of $t \mapsto (Wr(par,w)(t) + (-1)^{a_1} Wr(par,w)(-t))/t$ converges for $\mathrm{Re}\,s$ large and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$; `hWr4`, for each $b'$ equal to $par$ or to $par + P.\mathrm{centralSign}$, the same Mellin transform converges for $\mathrm{Re}\,s$ large and equals the archimedean factor of $P$ twisted by $(0,b')$. Whittaker laws for $WA$: `hWAN`, left equivariance under the unipotent $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ with factor $e^{-2\pi i a x}$; `hWAZ`, left equivariance under the scalar $z$ with factor $|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}}$; `hWAK`, right equivariance under the row-isometry subgroup by the weight character of $kw(par,\cdot)$ at the default place; `hWAt`, $WA(par)$ on the torus element $\mathrm{diag}(t,1)$ is $Wr(par)$ at the default place evaluated at $t$; and `hWAc`, continuity of $WA(par)$. Finally $w_{0R} \in \mathrm{GL}_2(\mathbb{R})$ is the antidiagonal involution $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀R`).
--
--   On the $K$ side, $w_0$ is a real place of $K$, and $P_2$ is an archimedean parameter satisfying `hP₂`: either $K$ has exactly three real places $w_0,w_1,w_2$, pairwise distinct and exhausting all infinite places, and $P_2 = \mathrm{principal}\,(uR\,w_1)\,(aR\,w_1)\,(uR\,w_2)\,(aR\,w_2)$; or the infinite places of $K$ are a complex place $w_C$ and $w_0$, and either $kC(w_C) \neq 0$ and $P_2$ is discrete with exponent $uC(w_C)$ and length $|kC(w_C)|$, or $kC(w_C) = 0$ and $P_2 = \mathrm{principal}\,(uC\,w_C)\,0\,(uC\,w_C)\,1$. A real archimedean Whittaker datum $D$ for $P_2$ and an integer $k_0$ are given with: `hDW`, right equivariance of $D.W$ under the row-isometry subgroup by the weight character of $k_0$; `hDE`, the Casimir eigenvalue equation $\mathrm{matrixCasimir}(D.W) = P_2.\mathrm{laplaceEigenvalue}\cdot D.W$ on invertible matrices; `hDnz`, $D.W$ is not identically zero; and `hk₀min`, in the principal case for $P_2$ one has $k_0 \in \{0,1\}$ with $k_0 \equiv a_1+a_2 \pmod 2$, and in the discrete case of length $m$ one has $k_0 = m+1$. The hypothesis `hLevi` requires that if $k_0 = 0$ then in the principal case for $P_2$ the first parity equals $b$.
--
--   The branch treated here is the weight-zero Levi branch: `hP₂eq` puts $P_2 = \mathrm{principal}\,u_1\,b\,u_2\,b$ with the same parity $b$ as $P$, and `hk₀` fixes $k_0 = 0$; accordingly $n \in \mathbb{N}$ with $n = k_0$ (`hn`), so $n = 0$. The integer $\delta$ is $0$ or $1$ (`hδ`) with $\delta \equiv aR(w_0) + b \pmod 2$ (`hδpar`), and the Schwartz datum $S$ on $2\times 3$ real matrices is, by `hS`, $$S(M) = (M_{00}M_{11}-M_{01}M_{10})^{\delta}\,(M_{02} - i\,M_{12})^{n}\,\mathrm{gaussian3}(M),$$ where $\mathrm{gaussian3}(M) = \exp(-\pi\sum_{i,j} M_{ij}^2)$. The constant $\rho \in \mathbb{C}$ is pinned by `hρ`: for every $\tau > 0$, $$D.W(\mathrm{diag}(\tau,1)) = \rho\,\tau\,\Bigl(4\int_{0}^{\infty} r^{u_1}e^{-\pi r^2}\,(\tau/r)^{u_2}e^{-\pi(\tau/r)^2}\,\frac{dr}{r}\Bigr).$$
--
--   The conclusion asserts the existence of an abscissa $\sigma_a \in \mathbb{R}$ such that for every $s$ with $\mathrm{Re}\,s > \sigma_a$ the dual torus-pair integral
--   $$\int_{a_2 > 0}\int_{a_1 \in \mathbb{R}} |\det q|\,WA(b)\bigl(w_{0R}\cdot {}^{t}q^{-1}\bigr)\cdot \bigl(\mathrm{dualWhittakerFn3}\;\mathrm{jacquetVector3}(D, uR(w_0), aR(w_0), a, \psi_\infty, S)\bigr)(q)\cdot |\det q|^{\,s-1/2}\cdot a_1^{-2}\,da_1\,da_2,$$
--   where $q = \begin{pmatrix} a_1 & 0 \\ 0 & a_2\end{pmatrix}$ for $a_1 \neq 0$ and $a_2 > 0$ (the integrand being $0$ otherwise), $^{t}q^{-1}$ is the transpose inverse, the dual Whittaker function is $g \mapsto W(w_{\mathrm{long}}\cdot {}^{t}g^{-1})$ in $\mathrm{GL}_3$, and $q$ is evaluated after embedding it into $\mathrm{GL}_2$ of the adeles at the real place of $\mathbb{Q}$, then into adelic $\mathrm{GL}_3$, then taking the archimedean component, equals
--   $$\Bigl(\varepsilon_\infty \cdot (-1)^{P.\mathrm{centralSign}}\cdot(-1)^{\#\{\text{complex places of }K\}}\Bigr)\cdot\bigl((-1)^{b}\,\pi\,\rho\bigr)\cdot \prod_{x}\Gamma_{\mathbb{R}}\bigl(s+\tfrac12+x\bigr)\cdot\prod_{y}\Gamma_{\mathbb{C}}\bigl(s+\tfrac12+y\bigr).$$
--   Here $\varepsilon_\infty$ is the archimedean root number of the family $(uR,aR,uC,kC)$ against the constant real parameter $P$ at the real places and its base change $P^{\mathrm{bc}}$ at the complex places, namely the product over real places of the epsilon factor of $P$ twisted by $(uR(w),aR(w))$ times the product over complex places of the epsilon factor of $P^{\mathrm{bc}}$ twisted by $(uC(w),kC(w))$. The first $\Gamma$-product runs over the multiset $\mathrm{twistedGammaR}$ formed from the duals of the constant real parameters, twisted by $(-uR,aR)$, and the second over the multiset $\mathrm{twistedGammaC}$ formed from the duals of the constant real and base-changed complex parameters, twisted by $(-uR,aR)$ and $(-uC,-kC)$ respectively.
--
--   This is the dual half of the archimedean torus-pair identity used in the Rankin–Selberg analysis of the cubic induction, for the even principal type in the weight-zero Levi branch: it identifies the dual unfolded $\mathrm{GL}_2 \times \mathrm{GL}_3$ torus integral, formed from the Jacquet vector of the Gaussian-times-harmonic datum $S$, with the archimedean root number times the explicit constant $(-1)^b\pi\rho$ times the dual twisted $\Gamma$-product. It feeds the combined statement [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3), where the same constant serves both the primal and the dual side and so yields the archimedean functional equation at the real place of $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightZero_profile.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightZero_profile
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
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA b (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = ((archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) * (((-1 : ℂ) ^ b.val * (Real.pi : ℂ)) * ρ)) * (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
                    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) := by sorry
