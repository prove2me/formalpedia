-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/ab6f98fc-7630-5083-a50d-f3c345d47824
-- title:
--   Dual torus pair unfolded for the block-harmonic section
-- statement:
--   The setting is a number field $K$ of degree $3$ over $\mathbb{Q}$ (the hypothesis `_hdeg` records $\operatorname{finrank}_{\mathbb Q} K = 3$), with $\mathcal O_K$ an integral $\mathcal O_{\mathbb Q}$-algebra, and a character $\mu : (\mathbb A_K)^\times \to \mathbb C^\times$ which is an admissible twist, i.e. trivial on $K^\times$, continuous and of absolute value $1$ (`_hμ`), subject to the non-descent hypothesis `_hns`: there is no admissible twist $\eta$ of $\mathbb Q$ such that at every $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and $\eta$ is unramified at $\mathfrak P \cap \mathcal O_{\mathbb Q}$ one has $\mu(\varpi_{\mathfrak P}) = \eta(\varpi_{\mathfrak P \cap \mathcal O_{\mathbb Q}})^{f}$, $f$ the inertia degree, where $\varpi$ denotes the uniformiser idele.
--
--   Archimedean data for $\mu$: functions $uR, aR$ on the real places and $uC, kC$ on the complex places of $K$, with $aR$ valued in $\mathbb Z/2$ and $kC$ in $\mathbb Z$, such that (`huR`, `huC`) for each real $w$ the local archimedean component of $\mu$ at $w$ is $x \mapsto \|x\|^{\mathrm{mult}(w)\,uR(w)}\,(x/\|x\|)^{(aR\,w).\mathrm{val}}$ and for each complex $w$ it is $x \mapsto \|x\|^{\mathrm{mult}(w)\,uC(w)}\,(x/\|x\|)^{kC(w)}$ (the predicate `IsArchCompAt`).
--
--   A character $\omega$ of $(\mathbb A_{\mathbb Q})^\times$ is given, with the three-part hypothesis `hω`: $\omega$ is an admissible twist of $\mathbb Q$; at every prime $p$ which is not a bad place for $(K,\mu)$ (not ramified in $K$, not twist-ramified above) $\omega$ is unramified and its Euler coefficient equals `inducedE3 ℚ (inducedCoeff K μ) p`, minus the coefficient of degree $3$ of the induced Euler polynomial; and, for every choice of archimedean data $uR, aR, uC, kC$ for $\mu$ as above, the archimedean component of $\omega$ at the real place of $\mathbb Q$ is given by the exponent $\sum_{w\ \mathrm{real}} uR(w) + \sum_{w\ \mathrm{complex}} 2\,uC(w)$ and the integer $\sum_{w\ \mathrm{real}} (aR\,w).\mathrm{val} + \sum_{w\ \mathrm{complex}} (kC(w)+1)$ (finite sums over the infinite places).
--
--   Auxiliary idelic and measure-theoretic data: a monoid homomorphism $E$ from the units of the infinite adeles of $\mathbb Q$ to the idele group, splitting the infinite part (`hE`: the infinite part of $E(u)$ is $u$ and its finite part is $1$); a rational number $a$ with $a \neq 0$ and $a = -1$; a unit $a_\infty$ of the infinite adeles with $a_\infty = a$; an additive character $\psi_\infty$ of the infinite adeles with $\psi_\infty(x) = \psi_{\mathrm{arch}}(a x)$ for the standard archimedean character; a measure $\nu_{\mathrm{add}}$ on the infinite adeles equal to $|a|^{1/2}$ times the pushforward of Lebesgue measure along the inverse of the identification of the infinite adeles with the mixed space; and a Haar measure $\nu_{\mathrm{mul}}$ on the units of the infinite adeles (measurability and Borel assumptions are routine).
--
--   The archimedean Whittaker package at the real place of $\mathbb Q$ consists of a real archimedean parameter $P$ (`RealArchParam`, either $\mathrm{principal}\,u_1\,a_1\,u_2\,a_2$ or $\mathrm{discrete}\,u\,k$) with `_hP₁` requiring $|\mathrm{Re}(u_1-u_2)| < 1$ in the principal case, together with weights $kw : \mathbb Z/2 \times \mathrm{InfinitePlace}\,\mathbb Q \to \mathbb Z$, radial functions $Wr$ and functions $WA$ on $\mathrm{GL}_2(\mathbb R)$, indexed by a parity $par \in \mathbb Z/2$, subject to the following hypotheses. Weights: `hkw1` says that in the principal case $kw(par,w) = \mathrm{signShift}(a_1+par) + \mathrm{signShift}(a_2+par)$ (where $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$), and `hkw2` that in the discrete case $kw(par,w) = n+1$. Radial functions: `hWr1` gives, for $P = \mathrm{principal}\,u_1\,a_1\,u_2\,a_1$ and $par = a_1$, the parity law $Wr(par,w,-t) = (-1)^{a_1.\mathrm{val}}\,Wr(par,w,t)$; `hWr2` gives vanishing on $t<0$ in the discrete case; `hWr3` gives, for $P$ principal with equal signs and $par = a_1+1$, an abscissa $s_0$ beyond which the Mellin transform of $t \mapsto (Wr(par,w,t) + (-1)^{a_1.\mathrm{val}} Wr(par,w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of `P.twist 0 a₁`; and `hWr4` gives, for $b = par$ or $b = par + P.\mathrm{centralSign}$, an abscissa beyond which the same Mellin transform converges and equals the archimedean factor of `P.twist 0 b`. Group-theoretic laws for $WA$: `hWAN` the unipotent law $WA(par, n(x)h) = e^{-2\pi i a x}\,WA(par,h)$; `hWAZ` the central law $WA(par, z\cdot h) = |z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{(P.\mathrm{centralSign}).\mathrm{val}}\,WA(par,h)$ for scalar $z$; `hWAK` the right equivariance $WA(par, h\kappa) = \mathrm{archWeightChar}_{\mathbb R}(kw(par,\mathrm{default}))(\kappa)\,WA(par,h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt` the identification $WA(par, \mathrm{diag}(t,1)) = Wr(par,\mathrm{default},t)$; and `hWAc` continuity of each $WA(par,\cdot)$.
--
--   Further data: the element $w_{0R} \in \mathrm{GL}_2(\mathbb R)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$; a real place $w_0$ of $K$; a second real archimedean parameter $P_2$ satisfying the dichotomy `hP₂`: either $K$ has exactly the three distinct real places $w_0,w_1,w_2$ and $P_2 = \mathrm{principal}\,(uR\,w_1)\,(aR\,w_1)\,(uR\,w_2)\,(aR\,w_2)$, or $K$ has exactly the places $w_C$ (complex) and $w_0$, and either $kC(w_C) \neq 0$ and $P_2 = \mathrm{discrete}\,(uC\,w_C)\,|kC(w_C)|$, or $kC(w_C) = 0$ and $P_2 = \mathrm{principal}\,(uC\,w_C)\,0\,(uC\,w_C)\,1$. Attached to $P_2$ is an archimedean datum $D$ of type `ArchDatumR P₂` (a Whittaker function $D.W$ on $2 \times 2$ real matrices with smoothness, unipotent and central laws, and the zeta-integral, functional-equation, finite-order and decay clauses of that structure) and an integer $k_0$ with: `hDW`, the right weight-$k_0$ law $D.W(x\kappa) = \mathrm{archWeightChar}_{\mathbb R}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, the Casimir eigenvalue equation $\mathrm{matrixCasimir}(D.W)(x) = P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x \neq 0$; `hDnz`, non-vanishing of $D.W$ at some point; and `hk₀min`, which requires $k_0 \in \{0,1\}$ with $k_0 \equiv a_1+a_2 \pmod 2$ in the principal case for $P_2$ and $k_0 = m+1$ in the discrete case. Finally `hPw1` requires $P$ to be principal with unequal signs $a_1 \neq a_2$, `hk₀` fixes $k_0 = 0$, `heven` requires $aR\,w_0 = a_1$ whenever $P_2 = \mathrm{principal}\,u_1\,a_1\,u_2\,a_2$, and $par_0 \in \mathbb Z/2$ is arbitrary.
--
--   The Schwartz-type section $S$ on $2\times 3$ real matrices is given by `hS` as
--   $$S(M) = \big((M_{00} + i M_{10}) - i (M_{01} + i M_{11})\big)\,(M_{02} - i M_{12})^{1}\,\exp\!\big(-\pi \textstyle\sum_{i,b} M_{ib}^2\big).$$
--
--   For every $s \in \mathbb C$ the assertion is an equality of iterated Lebesgue integrals over $a_2 \in (0,\infty)$ and $a_1 \in \mathbb R$, both integrands being defined by a case split which gives $0$ unless $a_1 \neq 0$ and $a_2 > 0$.
--
--   On the left, for $a_1 \neq 0$ and $a_2 > 0$ put $q = \mathrm{upperUnit}\,a_1\,0\,a_2 = \begin{pmatrix}a_1 & 0\\ 0 & a_2\end{pmatrix} \in \mathrm{GL}_2(\mathbb R)$; the integrand is
--   $$\Big(|\det q|\; WA\big(par_0,\; w_{0R}\cdot {}^t q^{-1}\big)\; \mathcal J^{\vee}\big(\iota(q)_\infty\big)\Big)\,|\det q|^{\,s-1/2}\,a_1^{-2},$$
--   where ${}^t q^{-1}$ is [`RSCarrier.transposeInv q`](def/LanglandsTunnell_RSCarrier.html#L31), where $\iota(q)_\infty$ is the archimedean component (`archComponent3`) of the image of $q$ under the embedding of $\mathrm{GL}_2(\mathbb R)$ at the real place of $\mathbb Q$ into the adelic $\mathrm{GL}_2$ followed by the block embedding `iota` into the adelic $\mathrm{GL}_3$, and where $\mathcal J^{\vee} = \mathrm{dualWhittakerFn3}(\mathcal J)$, i.e. $\mathcal J^{\vee}(g) = \mathcal J(w_3 \cdot {}^t g^{-1})$ with $w_3$ the long Weyl element of $\mathrm{GL}_3$, applied to the Jacquet vector $\mathcal J = \mathrm{jacquetVector3}\,D\,(uR\,w_0)\,(aR\,w_0)\,a\,\psi_\infty\,S$.
--
--   On the right, writing $u_0 = uR\,w_0$, $\varepsilon_0 = aR\,w_0$, $\chi_{u,\varepsilon}(y) = |y|^{u}\cdot(1$ if $\varepsilon = 0$, $\mathrm{sign}(y)$ otherwise$)$ for `ArchR.quasiChar`, and $\rho_0 = (e^{-1})_{10}$, $\rho_1 = (e^{-1})_{11}$ for $e \in M_2(\mathbb R)$, the integrand is
--   $$\Big(|a_1a_2|\cdot i^{\,kw(par_0,\mathrm{default})}\,|-a_1^{-1}|^{\,P.\mathrm{centralExponent}+1}\Big(\tfrac{-a_1^{-1}}{|-a_1^{-1}|}\Big)^{(P.\mathrm{centralSign}).\mathrm{val}}\,Wr\big(par_0,\mathrm{default},-a_1/a_2\big)\Big)$$
--   $$\times\;\chi_{u_0+1,\varepsilon_0}\big(-(a_1a_2)^{-1}\big)\int_{e \in M_2(\mathbb R)} G(e)\;\chi_{u_0+2,\varepsilon_0}(\det e)\,|\det e|^{-2}\;D.W\big(\mathrm{diag}(a,1)\,e^{-1}\big)\,de$$
--   $$\times\;|a_1a_2|^{\,s-1/2}\,a_1^{-2},$$
--   where
--   $$G(e) = (e_{00} - i e_{10})^{1}\,e^{-\pi\left(a_2^{-2}(e_{01}^2+e_{11}^2)+(e_{00}^2+e_{10}^2)\right)}\,\frac{a_1^{2}}{|\det e|}\,\big(-i\big)\Big(a\,a_1(\rho_0 + i\rho_1) + a_2^{-1}(e_{01}+i e_{11})\Big)\,e^{-\pi a^{2} a_1^{2}(\rho_0^{2}+\rho_1^{2})},$$
--   $\mathrm{diag}(a,1)$ being `ArchR.diagOne (a : ℝ)`. Thus the dual torus pair, with its $\mathrm{GL}_2$ Whittaker factor reflected by $w_{0R}$ and its $\mathrm{GL}_3$ dual Whittaker factor, is rewritten as the same $(a_1,a_2)$-integral with the three factors in explicit form and the remaining integration over $e \in M_2(\mathbb R)$.
--
--   This is the unfolding step, for the block-harmonic (degree-one column factor) section and the parameter $a = -1$, in the archimedean Rankin–Selberg analysis of the cubic induction used in the Langlands–Tunnell argument: it replaces the dual torus pair by an explicit iterated integral in Siegel coordinates $(a_1,a_2)$ with an inner matrix integral. It feeds the statement [`LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile`](thm.html#LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile), which identifies the resulting quantity with an archimedean root number times a gamma factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3.lean

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

theorem LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3
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
    (s : ℂ) :
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
      = (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                ((((|a₁ * a₂| : ℝ) : ℂ) *
                    (Complex.I ^ (kw par₀ default) *
                      ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
                        ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) *
                      Wr par₀ default (-a₁ / a₂))) *
                  (ArchR.quasiChar (uR w₀ h₀ + 1) (aR w₀ h₀) (-(a₁ * a₂)⁻¹) *
                    ∫ e : Fin 2 → Fin 2 → ℝ,
                      ((((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ 1 *
                    (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
                    (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
                    (-Complex.I *
                      ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) +
                        (a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) + Complex.I * ((e 1 1 : ℝ) : ℂ)))) *
                    (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
                        (ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) *
                        D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹)) *
                  (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0) := by sorry
