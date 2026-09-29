-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_ne_zero_and_W_diagOne_eq_mul_exp_and_eq_zero_of_discreteLevi
-- name    : LanglandsTunnell.Converse.exists_ne_zero_and_W_diagOne_eq_mul_exp_and_eq_zero_of_discreteLevi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/0085ebaf-89c1-508c-b488-e19393103353
-- title:
--   Non-vanishing scalar in the discrete-series Whittaker profile
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$, and let $\mu$ be a character of the idele class group of $K$ with values in $\mathbb{C}^\times$ which is admissible in the sense that it kills the image of $K^\times$, is continuous and is unitary. Its archimedean components are given by exponents: for each real place $w$ by a pair $(uR\,w, aR\,w)\in\mathbb{C}\times\mathbb{Z}/2$ and for each complex place $w$ by $(uC\,w, kC\,w)\in\mathbb{C}\times\mathbb{Z}$, in the sense that the local character of $\mu$ at $w$ is $x\mapsto \|x\|^{\mathrm{mult}(w)u}(x/\|x\|)^{a}$; $\omega$ is a character of the idele class group of $\mathbb{Q}$ whose archimedean exponents at the real place are the sums $\sum_w uR\,w+\sum_w 2\,uC\,w$ and $\sum_w (aR\,w).\mathrm{val}+\sum_w (kC\,w+1)$. Further data are assumed: a splitting $E$ of the infinite part of the ideles of $\mathbb{Q}$ (infinite part of $E(u)$ equal to $u$, finite part trivial), a nonzero rational $a$ with an idele $aInf$ representing it, the additive character $\psi_\infty(x)=\psi_{\mathrm{arch}}(ax)$, an additive measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the mixed-space ring equivalence, and a Haar measure $\nu_{\mathrm{mul}}$. Let $w_0$ be a real place of $K$, and let $P_2$ be a real archimedean parameter arising from the remaining places in the two admissible shapes: either $K$ has three real places $w_0,w_1,w_2$ and $P_2$ is the principal parameter $(uR\,w_1,aR\,w_1,uR\,w_2,aR\,w_2)$, or $K$ has one real place $w_0$ and one complex place $w_C$, and $P_2$ is the discrete parameter $(uC\,w_C,|kC\,w_C|)$ when $kC\,w_C\neq 0$, respectively the principal parameter $(uC\,w_C,0,uC\,w_C,1)$ when $kC\,w_C=0$. Let $D$ be an archimedean Whittaker datum for $P_2$, that is, a smooth function $W$ on invertible real $2\times 2$ matrices transforming by $\psi$ under left unipotents and by the central character of $P_2$ under scalars, with entire, functional-equation-satisfying, finite-order zeta integrals and the prescribed growth bounds. Assume $W$ transforms under the right action of the row-isometry subgroup by the weight character $\mathrm{archWeightChar}_{\mathbb{R}}$ of an integer $k_0$, that $W$ is an eigenfunction of the matrix Casimir operator with eigenvalue $P_2.\mathrm{laplaceEigenvalue}$, that $W$ does not vanish identically, and that $k_0$ is minimal in the stated normalised sense ($k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2$ in the principal case, $k_0=m+1$ in the discrete case). Finally assume $P_2$ is the discrete parameter attached to $\mu'\in\mathbb{C}$ and $k\geq 1$. Then there exists $\rho\in\mathbb{C}$ with $\rho\neq 0$ such that $W(\mathrm{diag}(\tau,1))=\rho\cdot 2\bigl(\tau^{\mu'+k/2+1}e^{-2\pi\tau}\bigr)$ for all $\tau>0$ and $W(\mathrm{diag}(-\tau,1))=0$ for all $\tau>0$.
--
--   This is the archimedean Whittaker profile in the discrete-series branch: on the positive torus the function is the classical Whittaker function $\tau^{\mu'+k/2+1}e^{-2\pi\tau}$ of a holomorphic discrete series of weight $k+1$, vanishing on the negative torus, and here the constant is asserted to be nonzero. It feeds the archimedean input of the cubic-induction construction of a nonvanishing Jacquet vector for the admissible twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_ne_zero_and_W_diagOne_eq_mul_exp_and_eq_zero_of_discreteLevi.lean

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

theorem LanglandsTunnell.Converse.exists_ne_zero_and_W_diagOne_eq_mul_exp_and_eq_zero_of_discreteLevi
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
    (μ' : ℂ) (k : ℕ) (hk : 1 ≤ k) (hP₂eq : P₂ = RealArchParam.discrete μ' k hk) :
    ∃ ρ : ℂ, ρ ≠ 0 ∧ (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (μ' + (k : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ)))) ∧
      (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0) := by sorry
