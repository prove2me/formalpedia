-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
-- name    : LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/bb45f72b-7c36-578b-a8de-b9c72a3a2812
-- title:
--   Non-vanishing archimedean zeta integral, weight-zero Levi branch
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ and let $\mu$ be a character of the idele units of $K$ which is trivial on $K^\times$, continuous and unitary; suppose its archimedean component at each real place $w$ is $x\mapsto \|x\|^{w.\mathrm{mult}\cdot uR(w)}(x/\|x\|)^{(aR(w)).\mathrm{val}}$ and at each complex place $\|x\|^{w.\mathrm{mult}\cdot uC(w)}(x/\|x\|)^{kC(w)}$, and let $\omega$ be a character of the idele units of $\mathbb{Q}$ whose component at each real place has exponent $\sum_w uR(w)+\sum_w 2\,uC(w)$ and integer parameter $\sum_w (aR(w)).\mathrm{val}+\sum_w (kC(w)+1)$. Let $E$ be a monoid map from the infinite ideles of $\mathbb{Q}$ into the ideles splitting the infinite part ($\mathrm{infPart}(E u)=u$, $\mathrm{finPart}(E u)=1$), let $a\in\mathbb{Q}^\times$ with a unit $a_\infty$ over it, let $\psi_\infty=\psi_{\mathrm{arch}}(a\,\cdot)$, let $\nu_{\mathrm{add}}$ be $|a|^{1/2}$ times the transport of Lebesgue measure along the mixed-space identification, and let $\nu_{\mathrm{mul}}$ be a Haar measure on the infinite idele units. Fix a real place $w_0$ and a parameter $P_2$ which is either the principal parameter built from the two remaining real places or, when the other place is complex, the discrete parameter of weight $|kC|$ (or the principal parameter $(uC,0,uC,1)$ when $kC=0$). Let $D$ be an `ArchDatumR` for $P_2$ (a Whittaker function $W$ on $2\times2$ real matrices, smooth on the invertible locus, with unipotent and central transformation laws, entire zeta integrals satisfying a functional equation, and the stated growth and decay bounds), transforming under right translation by `rowIsometrySubgroup₀` by the weight character of $k_0$, Casimir-eigen with eigenvalue $P_2.\mathrm{laplaceEigenvalue}$, not identically zero, with $k_0$ minimal in the sense that $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2$ for principal $P_2$ and $k_0=m+1$ for discrete $P_2$ of weight $m$. Let $m\ge1$, and let $n\in\mathbb{N}$, $\varepsilon'$ satisfy $(\varepsilon',n)=(-1,k_0-m)$ or $(1,m-k_0)$, and let $S(M)=((M_{00}-iM_{10})-i(M_{01}-iM_{11}))^m(M_{02}+\varepsilon' iM_{12})^n\,\mathrm{gaussian3}(M)$. Assume finally $k_0=0$, $P_2=\mathrm{principal}\,\mu_1\,c\,\mu_2\,c$, and that for all $\tau>0$ one has $W(\mathrm{diag}(\tau,1))=\rho\,\tau\cdot 4\int_0^\infty r^{\mu_1}e^{-\pi r^2}(\tau/r)^{\mu_2}e^{-\pi(\tau/r)^2}\,dr/r$ with $\rho\neq0$ (so that $\varepsilon'=1$ and $n=m$, the other alternative being numerically impossible). Then there exist a character $\sigma$ of the idele units of $\mathbb{Q}$ that is trivial on $\mathbb{Q}^\times$, continuous and unitary, and $s\in\mathbb{C}$, such that the $GL_3\times GL_1$ archimedean zeta integral $\int y\mapsto J(\iota(\mathrm{diag}(y,1))\cdot 1)\,\sigma(E y)\,\|y\|^{s-1}\,d\nu_{\mathrm{mul}}$ of the Jacquet vector $J=\mathrm{jacquetVector3}\,D\,(uR\,w_0)\,(aR\,w_0)\,a\,\psi_\infty\,S$ is non-zero.
--
--   This is the non-vanishing input for the archimedean $GL_3\times GL_1$ Rankin–Selberg integral of the Jacquet–Whittaker vector attached to the explicit flat section of degree $m$, in the branch where the $SO(2)$-weight is zero and the parameter is a principal-series parameter with equal sign characters and a Whittaker function whose restriction to the diagonal torus is the explicit Bessel-type integral. It feeds the corresponding unconditional statement in which these Levi-profile hypotheses are discharged, and so into the converse-theorem verification of the archimedean local factors used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi.lean

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

theorem LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
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
    (ha : a ≠ 0)
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
    (m : ℕ) (hm : 1 ≤ m)
    (n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)

    (hk₀ : k₀ = 0) (μ₁ μ₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal μ₁ c μ₂ c) (ρ : ℂ)
    (hD : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hρ0 : ρ ≠ 0) :
    ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
      ∃ s : ℂ, archZeta30 ν_mul (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (σ.comp E) s 1 ≠ 0 := by sorry
