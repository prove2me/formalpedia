-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_discreteLevi
-- name    : LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_discreteLevi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/41623578-37e3-512e-bdd1-7b99aefc2d52
-- title:
--   Admissible twist with non-vanishing archimedean zeta, discrete branch
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$, let $\mu$ be a character of the idele units of $K$ which is an admissible twist (trivial on principal ideles, continuous, of absolute value $1$), and let archimedean data $uR(w)\in\mathbb{C}$, $aR(w)\in\mathbb{Z}/2$ at the real places and $uC(w)\in\mathbb{C}$, $kC(w)\in\mathbb{Z}$ at the complex places be given, such that at each place the local component of $\mu$ on $(K_w)^\times$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$ with the corresponding exponents. Let $\omega$ be a character of the idele units of $\mathbb{Q}$ whose component at each real place has exponents $\sum_w uR(w)+\sum_w 2\,uC(w)$ and $\sum_w aR(w)+\sum_w (kC(w)+1)$, and let $E$ be a homomorphism from the infinite ideles of $\mathbb{Q}$ to the ideles splitting the infinite part and sending the finite part to $1$. Let $a\in\mathbb{Q}$, $a\neq 0$, let $aInf$ be an infinite idele equal to the image of $a$, let $psiInf$ be the additive character $x\mapsto \psi_{\mathrm{arch}}(a x)$, let $\nu_{\mathrm{add}}$ be $|a|^{1/2}$ times the transport of Lebesgue measure under the mixed-space identification, and let $\nu_{\mathrm{mul}}$ be a Haar measure on the infinite idele units. Let $w_0$ be a real place, and let $P_2$ be a real archimedean parameter subject to the alternative: either there are two further real places $w_1,w_2$, with $w_0,w_1,w_2$ distinct and exhausting the infinite places, and $P_2$ is the principal parameter built from $(uR,aR)$ at $w_1,w_2$; or there is a complex place $wC$ with $wC,w_0$ exhausting the infinite places and $P_2$ is $\mathrm{discrete}(uC(wC),|kC(wC)|)$ when $kC(wC)\neq 0$, respectively $\mathrm{principal}(uC(wC),0,uC(wC),1)$ when $kC(wC)=0$. Let $D$ be an archimedean Whittaker datum for $P_2$ (a function $W$ on real $2\times 2$ matrices, smooth on the invertible locus, transforming by $\psi$ under left unipotents and by the central character of $P_2$ under scalars, with entire twisted zeta integrals satisfying the functional equation, finite order and the prescribed decay), let $k_0\in\mathbb{Z}$ be such that $W(x r)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(r)\,W(x)$ for $r$ in the row-isometry subgroup, let $W$ be an eigenfunction of the matrix Casimir with eigenvalue $P_2.\mathrm{laplaceEigenvalue}$, let $W$ be not identically zero, and let $k_0$ be minimal in the sense that $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2$ in the principal case and $k_0=m+1$ in the discrete case $\mathrm{discrete}(u,m)$. Let $m\geq 1$, and let $n\in\mathbb{N}$, $\varepsilon'\in\mathbb{R}$ satisfy either $\varepsilon'=-1$, $n=k_0-m$, or $\varepsilon'=1$, $n=m-k_0$; let $S$ be the Schwartz section on $2\times 3$ real matrices given by $((M_{00}-iM_{10})-i(M_{01}-iM_{11}))^{m}\,(M_{02}+\varepsilon' i M_{12})^{n}\,\mathrm{gaussian3}(M)$. Assume finally that $P_2=\mathrm{discrete}(\mu,k)$ for a complex number $\mu$ (the name shadows the character above) and an integer $k\geq 1$, and that for some $\rho\neq 0$ one has $D.W(\mathrm{diagOne}(\tau))=2\rho\,\tau^{\mu+k/2+1}e^{-2\pi\tau}$ for all $\tau>0$ and $D.W(\mathrm{diagOne}(-\tau))=0$ for all $\tau>0$. Then there exist an admissible twist $\sigma$ of the ideles of $\mathbb{Q}$ and an $s\in\mathbb{C}$ such that the $GL_3\times GL_1$ archimedean zeta integral $\mathrm{archZeta30}$, taken against $\nu_{\mathrm{mul}}$ of the Jacquet vector $\mathrm{jacquetVector3}\,D\,(uR(w_0))\,(aR(w_0))\,a\,psiInf\,S$ twisted by $\sigma\circ E$, is non-zero at $s$ and at the identity of $GL_3$.
--
--   This is the non-vanishing input for the archimedean place in the cubic-induction step of the Langlands–Tunnell argument: it produces a twist of the ideles of $\mathbb{Q}$ for which the $GL_3\times GL_1$ zeta integral of the explicit degree-$m$ flat Jacquet vector does not vanish identically, in the branch where the Levi parameter is of discrete type with an explicitly prescribed Whittaker function on the positive diagonal. It is used by the companion statement in which the explicit discrete-series profile is no longer assumed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_discreteLevi.lean

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

theorem LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_discreteLevi
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

    (μ : ℂ) (k : ℕ) (hk : 1 ≤ k) (hP₂eq : P₂ = RealArchParam.discrete μ k hk) (ρ : ℂ)
    (hDpos : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (μ + (k : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ))))
    (hDneg : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0)
    (hρ0 : ρ ≠ 0) :
    ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
      ∃ s : ℂ, archZeta30 ν_mul (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (σ.comp E) s 1 ≠ 0 := by sorry
