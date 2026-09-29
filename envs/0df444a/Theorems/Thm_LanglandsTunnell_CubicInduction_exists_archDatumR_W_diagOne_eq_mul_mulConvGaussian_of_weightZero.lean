-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archDatumR_W_diagOne_eq_mul_mulConvGaussian_of_weightZero
-- name    : LanglandsTunnell.CubicInduction.exists_archDatumR_W_diagOne_eq_mul_mulConvGaussian_of_weightZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/27fbff7e-64f0-5d29-8fa9-7731aa0b2690
-- title:
--   Weight-zero torus profile is a Gaussian multiplicative convolution
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$, let $\mu$ be a character of the idele units of $K$ into $\mathbb{C}^\times$ which is trivial on principal ideles, continuous and unitary, and let $u_R(w),a_R(w)\in\mathbb{C}\times\mathbb{Z}/2$ for real places $w$ and $u_C(w)\in\mathbb{C},k_C(w)\in\mathbb{Z}$ for complex places $w$ describe the archimedean components of $\mu$ in the sense of `IsArchCompAt`, i.e. on units $x$ of $K_w$ the local component of $\mu$ is $\|x\|^{\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$ for the corresponding pair $(u,a)$. Let $\omega$ be a character of the rational ideles whose real archimedean components are given by $(u,a)$ the sums $\sum_w u_R(w)+\sum_w 2u_C(w)$ and $\sum_w a_R(w)+\sum_w (k_C(w)+1)$; let $E$ split the infinite-adele units into ideles with the given infinite part and trivial finite part; let $a\in\mathbb{Q}$ be non-zero with unit lift $a_\infty$, let $\psi_\infty$ be the additive character $x\mapsto \psi_{\mathrm{arch}}(ax)$, and let $\nu_{\mathrm{add}}$ be $|a|^{1/2}$ times the transported Lebesgue measure on the infinite adeles and $\nu_{\mathrm{mul}}$ a Haar measure on their units. Fix a real place $w_0$ of $K$ and a real archimedean parameter $P_2$ attached, by the stated case distinction in $hP_2$, to the remaining places: either $K$ has three real places and $P_2=\mathrm{principal}(u_R(w_1),a_R(w_1),u_R(w_2),a_R(w_2))$, or $K$ has one complex place $w_C$ and $P_2$ is $\mathrm{discrete}(u_C(w_C),|k_C(w_C)|)$ when $k_C(w_C)\neq 0$ and $\mathrm{principal}(u_C(w_C),0,u_C(w_C),1)$ when $k_C(w_C)=0$. Let $D$ be an `ArchDatumR` for $P_2$, that is a function $W$ on real $2\times 2$ matrices, smooth on the invertible locus, with the unipotent law $W(n(x)g)=\psi(x)W(g)$, the central law $W(zg)=\chi_{P_2}(z)|z|W(g)$, entire completed zeta integrals with archimedean factor and $\varepsilon$-functional equation, and the prescribed decay at infinity and near zero. Assume $W$ transforms under the row-isometry subgroup of $\mathrm{GL}_2(\mathbb{R})$ by the character $\mathrm{archWeightChar}_{\mathbb{R}}$ of weight $k_0$, that $W$ is a Casimir eigenfunction with eigenvalue $P_2.\mathrm{laplaceEigenvalue}$ on invertible matrices, that $W$ does not vanish identically, that $k_0$ satisfies the minimality constraints $hk_{0}\mathrm{min}$ (in the principal case $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \bmod 2$, in the discrete case $k_0=m+1$), that $k_0=0$, and that $P_2=\mathrm{principal}(u_1,c_1,u_2,c_2)$. Then there exists $\rho\in\mathbb{C}$ such that for every real $\tau>0$ $$W\begin{pmatrix}\tau&0\\0&1\end{pmatrix}=\rho\,\tau\cdot 4\int_0^\infty r^{u_1}e^{-\pi r^2}\,(\tau/r)^{u_2}e^{-\pi(\tau/r)^2}\,\frac{dr}{r}.$$
--
--   This identifies the torus profile of a weight-zero archimedean Whittaker datum with the canonical Gaussian multiplicative convolution, i.e. the classical $K$-Bessel profile $4\tau^{(u_1+u_2)/2}K_{(u_1-u_2)/2}(2\pi\tau)$, up to a single complex scalar; the companion statement [`LanglandsTunnell.CubicInduction.archDatumR_W_diagOne_neg_eq_of_weightZero`](thm.html#LanglandsTunnell.CubicInduction.archDatumR_W_diagOne_neg_eq_of_weightZero) records the behaviour on the negative sheet. It is used in the Rankin–Selberg unfolding computations for principal and discrete-series parameters and in the converse-theorem step for the weight-zero Levi parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_archDatumR_W_diagOne_eq_mul_mulConvGaussian_of_weightZero.lean

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

theorem LanglandsTunnell.CubicInduction.exists_archDatumR_W_diagOne_eq_mul_mulConvGaussian_of_weightZero
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
    (hk₀ : k₀ = 0)
    (u₁ u₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c₁ u₂ c₂) :
    ∃ ρ : ℂ, ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)) := by sorry
