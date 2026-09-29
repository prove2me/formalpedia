-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_ne_zero_and_W_diagOne_eq_mul_mulConvGaussian_of_weightZeroLevi
-- name    : LanglandsTunnell.Converse.exists_ne_zero_and_W_diagOne_eq_mul_mulConvGaussian_of_weightZeroLevi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/e568ff57-d001-5e1d-abf1-dcba6bb25e14
-- title:
--   Non-vanishing scalar in the weight-zero torus profile
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ and let $\mu$ be a character of the idele units of $K$ which is trivial on principal ideles, continuous and unitary. Data $uR,aR$ at the real places and $uC,kC$ at the complex places are assumed to describe the archimedean local components of $\mu$ in the sense of `IsArchCompAt` (at $w$ the local character is $x\mapsto \|x\|^{(\mathrm{mult}\,w)u}(\iota_w(x)/\|x\|)^{a}$), and $\omega$ is a character over $\mathbb{Q}$ whose real archimedean component is given by the finsums $\sum uR+\sum 2uC$ and $\sum aR.\mathrm{val}+\sum(kC+1)$. Further data: a homomorphism $E$ splitting the infinite part of the rational ideles with trivial finite part, a nonzero rational $a$ with its infinite idele $aInf$, the additive character $\psi_\infty(x)=\psi_{\mathrm{arch}}(ax)$, the additive measure $\nu_{\mathrm{add}}=|a|^{1/2}$ times the pushforward of Lebesgue measure from the mixed space, and a Haar measure $\nu_{\mathrm{mul}}$ on the infinite idele units. Let $w_0$ be a real place of $K$ and let $P_2$ be a real archimedean parameter arising, via the hypothesis `hP₂`, either from two further real places of $K$ besides $w_0$ (principal parameter built from $uR,aR$ there) or from a complex place $w_C$ together with $w_0$ (discrete parameter with $|kC(w_C)|$ when $kC(w_C)\neq0$, principal $(uC,0;uC,1)$ otherwise). Let $D$ be an `ArchDatumR` for $P_2$, that is a Whittaker-type function $W$ on $2\times 2$ real matrices with the unipotent, central, smoothness, zeta-integral, functional-equation and decay properties recorded in that structure, and let $k_0$ be an integer such that $W(xr)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(r)\,W(x)$ for $r$ in `rowIsometrySubgroup₀ ℝ` and $x\in\mathrm{GL}_2(\mathbb{R})$, such that $W$ is an eigenfunction of the matrix Casimir operator with eigenvalue $P_2.\mathrm{laplaceEigenvalue}$ on invertible matrices, such that $W$ does not vanish identically, and such that $k_0$ satisfies the minimality constraints $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \pmod 2$ in the principal case and $k_0=m+1$ in the discrete case. Assume finally $k_0=0$ and $P_2=\mathrm{principal}(\mu_1,c,\mu_2,c)$. Then there is a complex number $\rho\neq0$ such that for every $\tau>0$ $$W\begin{pmatrix}\tau&0\\0&1\end{pmatrix}=\rho\,\tau\cdot 4\int_0^\infty r^{\mu_1}e^{-\pi r^2}\,(\tau/r)^{\mu_2}e^{-\pi(\tau/r)^2}\,\frac{dr}{r}.$$
--
--   This is the archimedean torus profile of a weight-zero principal-series Whittaker datum: on the positive torus the function $\tau\mapsto W(\mathrm{diag}(\tau,1))$ is a nonzero multiple of $\tau$ times the multiplicative convolution of two Gaussians with exponents $\mu_1,\mu_2$. It strengthens the corresponding existence statement by recording that the scalar is nonzero, and serves as the profile input for the construction of a nonvanishing Jacquet vector attached to an admissible twist over a cubic field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_ne_zero_and_W_diagOne_eq_mul_mulConvGaussian_of_weightZeroLevi.lean

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

theorem LanglandsTunnell.Converse.exists_ne_zero_and_W_diagOne_eq_mul_mulConvGaussian_of_weightZeroLevi
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
    (hk₀ : k₀ = 0) (μ₁ μ₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal μ₁ c μ₂ c) :
    ∃ ρ : ℂ, ρ ≠ 0 ∧ (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ))) := by sorry
