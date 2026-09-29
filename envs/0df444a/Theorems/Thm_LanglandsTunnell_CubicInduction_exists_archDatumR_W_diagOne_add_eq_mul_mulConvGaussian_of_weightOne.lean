-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archDatumR_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOne
-- name    : LanglandsTunnell.CubicInduction.exists_archDatumR_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/ffb36558-7398-5a62-965b-b1801856adae
-- title:
--   Weight-one torus profile as Gaussian multiplicative convolution
-- statement:
--   The setting is a number field $K$ of degree $3$ over $\mathbb{Q}$ together with: a character $\mu$ of the idele class group of $K$ which is trivial on principal ideles, continuous and unitary; complex numbers $uR\,w$ and classes $aR\,w \in \mathbb{Z}/2$ at the real places, complex numbers $uC\,w$ and integers $kC\,w$ at the complex places, such that at each place the local archimedean component of $\mu$ on $x$ is $\|x\|^{\mathrm{mult}(w)\,u}$ times $(\iota_w(x)/\|x\|)^{a}$ with the indicated exponents; a character $\omega$ of the ideles of $\mathbb{Q}$ whose real archimedean component has exponent $\sum_{w \text{ real}} uR\,w + \sum_{w \text{ complex}} 2\,uC\,w$ and integer parameter $\sum_{w \text{ real}} (aR\,w).\mathrm{val} + \sum_{w \text{ complex}} (kC\,w + 1)$; a splitting $E$ of the infinite ideles into ideles with trivial finite part; a nonzero rational $a$ with its infinite idelic image $aInf$, the additive character $\psi_{\infty}(x) = \psi_{\mathrm{arch}}(ax)$, and measures $\nu_{\mathrm{add}} = |a|^{1/2}$ times the transported Lebesgue measure on the mixed space and a Haar measure $\nu_{\mathrm{mul}}$ on the infinite idele units (these data are summarised here as the ambient global setting). Further, $w_0$ is a real place of $K$ and $P_2$ a real archimedean parameter constrained by $hP_2$: either $K$ has exactly the three distinct real places $w_0, w_1, w_2$ and $P_2 = \mathrm{principal}(uR\,w_1, aR\,w_1, uR\,w_2, aR\,w_2)$, or $K$ has exactly one complex place $w_C$ besides $w_0$ and $P_2 = \mathrm{discrete}(uC\,w_C, |kC\,w_C|)$ when $kC\,w_C \neq 0$, while $P_2 = \mathrm{principal}(uC\,w_C, 0, uC\,w_C, 1)$ when $kC\,w_C = 0$. Finally $D$ is an archimedean Whittaker datum of type $P_2$ (a smooth function $W$ on $2\times 2$ real matrices with the unipotent character law, the central law, entire zeta functions satisfying the functional equation with $\varepsilon$-factor of $P_2$, finite order in vertical strips, and the prescribed decay), $k_0$ an integer with $W(x r) = \mathrm{archWeightChar}_{\mathbb{R}}(k_0)(r)\,W(x)$ for $r$ in the row-isometry subgroup, with $W$ a Casimir eigenfunction of eigenvalue $P_2.\mathrm{laplaceEigenvalue}$, with $W$ not identically zero, with $k_0$ subject to the minimality constraints ($k_0 \in \{0,1\}$ and $k_0 \equiv a_1 + a_2$ in the principal case, $k_0 = m+1$ in the discrete case), and with $k_0 = 1$; moreover $P_2 = \mathrm{principal}(u_1, c_1, u_2, c_2)$ with $c_1 \neq c_2$. The conclusion asserts the existence of a single $\rho \in \mathbb{C}$ such that for every $b \in \mathbb{Z}/2$ and every $\tau > 0$ $$W(\mathrm{diag}(\tau,1)) + (-1)^{b}\,W(\mathrm{diag}(-\tau,1)) = \rho\,\tau \cdot 4\int_{0}^{\infty} r^{u_1 + [c_1+b]} e^{-\pi r^2}\,(\tau/r)^{u_2 + [c_2+b]} e^{-\pi (\tau/r)^2}\,\frac{dr}{r},$$ where $[c] = 0$ for $c = 0$ and $[c] = 1$ otherwise. Thus both sheet combinations of the torus profile are multiples, by one common scalar, of the multiplicative Gaussian convolutions attached to the shifted exponents.
--
--   This is the archimedean input of the weight-one case in the Langlands–Tunnell converse-theorem construction: it identifies the torus profile of a minimal-weight Whittaker datum of principal type with opposite sign characters as an explicit multiplicative convolution of two Gaussians, a single proportionality constant serving both parities. It is used downstream in the Rankin–Selberg unfolding computations and in the non-vanishing statements for the weight-one Levi datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_archDatumR_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOne.lean

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

theorem LanglandsTunnell.CubicInduction.exists_archDatumR_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOne
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
    (hk₀ : k₀ = 1)
    (u₁ u₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c₁ u₂ c₂) (hc : c₁ ≠ c₂) :
    ∃ ρ : ℂ, ∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (u₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)) := by sorry
