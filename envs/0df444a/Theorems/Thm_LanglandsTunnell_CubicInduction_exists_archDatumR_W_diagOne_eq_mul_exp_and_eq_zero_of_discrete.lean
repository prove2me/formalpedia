-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archDatumR_W_diagOne_eq_mul_exp_and_eq_zero_of_discrete
-- name    : LanglandsTunnell.CubicInduction.exists_archDatumR_W_diagOne_eq_mul_exp_and_eq_zero_of_discrete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/18047b85-3627-5177-add7-4023ee44f1f8
-- title:
--   Discrete-series torus profile of a real archimedean Whittaker datum
-- statement:
--   Fix a number field $K$ of degree $3$ over $\mathbb{Q}$. The statement carries the global data of the cubic-induction setting, summarised here: a character $\mu$ of the idele units of $K$ which is trivial on principal ideles, continuous and unitary; complex numbers $uR_w$ and classes $aR_w \in \mathbb{Z}/2$ at the real places, complex numbers $uC_w$ and integers $kC_w$ at the complex places, such that at each infinite place the local component of $\mu$ on $x \in (K_w)^\times$ equals $\|x\|^{\mathrm{mult}(w)\,u}(x/\|x\|)^{a}$ with the corresponding parameters; a character $\omega$ of the idele units of $\mathbb{Q}$ whose real components have parameters $\sum_w uR_w + \sum_w 2\,uC_w$ and $\sum_w aR_w + \sum_w (kC_w+1)$; a monoid homomorphism $E$ splitting the infinite ideles with infinite part the identity and trivial finite part; a nonzero rational $a$ together with the corresponding unit $a_\infty$ of the infinite adele ring, the additive character $x \mapsto \mathrm{psiArch}(a x)$, measurability and Borel hypotheses, a scaled pushforward measure $\nu_{\mathrm{add}}$ of Lebesgue measure and a Haar measure $\nu_{\mathrm{mul}}$ on the infinite idele units. Further, $w_0$ is a real place of $K$, and $P_2$ is a real archimedean parameter arising either from two further real places $w_1 \ne w_2$ exhausting the places of $K$, as $\mathrm{principal}(uR_{w_1},aR_{w_1},uR_{w_2},aR_{w_2})$, or from a complex place $w_C$ with the places of $K$ exactly $\{w_C,w_0\}$, as $\mathrm{discrete}(uC_{w_C},|kC_{w_C}|)$ when $kC_{w_C}\ne 0$ and as $\mathrm{principal}(uC_{w_C},0,uC_{w_C},1)$ when $kC_{w_C}=0$. Let $D$ be an `ArchDatumR` for $P_2$, that is, a function $W$ on $2\times 2$ real matrices, smooth on the non-singular locus, with $W(\mathrm{unip}(x)g)=\psi(x)W(g)$ and the central law $W(zg)=\mathrm{centralChar}(P_2)(z)\,|z|\,W(g)$ for $z \ne 0$, equipped with entire zeta functions representing the Tate integrals $\int W(\mathrm{diag}(y,1)g)\,\mathrm{quasiChar}_{u,a}(y)|y|^{s-1}\,dy/|y|$ as $\mathrm{archFactor}$ times an entire function, satisfying a functional equation under the Weyl element, finite order in vertical strips, and decay estimates on the torus. Let $k_0$ be an integer such that $W(xr)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(r)\,W(x)$ for all $r$ in `rowIsometrySubgroup₀ ℝ` and all $x \in \mathrm{GL}_2(\mathbb{R})$, such that the Casimir operator `matrixCasimir` acts on $W$ on the non-singular locus by the eigenvalue $P_2.\mathrm{laplaceEigenvalue}$, such that $W$ is not identically zero, and such that $k_0$ is minimal for $P_2$ in the sense that $k_0 \in \{0,1\}$ with $k_0 \equiv a_1+a_2 \pmod 2$ whenever $P_2 = \mathrm{principal}(u_1,a_1,u_2,a_2)$, and $k_0 = m+1$ whenever $P_2 = \mathrm{discrete}(u,m)$. Assume finally $P_2 = \mathrm{discrete}(u,k)$ with $k \ge 1$. Then there is $\rho \in \mathbb{C}$ with $W(\mathrm{diag}(\tau,1)) = \rho\cdot 2\,\tau^{\,u+k/2+1}e^{-2\pi\tau}$ for all real $\tau>0$, and $W(\mathrm{diag}(-\tau,1))=0$ for all real $\tau>0$.
--
--   This identifies the torus profile of an archimedean Whittaker datum of discrete-series type at minimal weight $k_0=k+1$: it is supported on the sheet of positive determinant and is a scalar multiple of the explicit discrete-series profile $2\,\tau^{u+k/2+1}e^{-2\pi\tau}$, the normalisation matching the Mellin transform of the corresponding archimedean $\Gamma$-factor. It feeds the converse-theorem and Rankin–Selberg steps of the Langlands–Tunnell argument, in particular the non-vanishing statement for the sum of the two torus profiles and the identification of archimedean $\Gamma$-factors for a cubic field with one complex place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_archDatumR_W_diagOne_eq_mul_exp_and_eq_zero_of_discrete.lean

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

theorem LanglandsTunnell.CubicInduction.exists_archDatumR_W_diagOne_eq_mul_exp_and_eq_zero_of_discrete
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
    (u : ℂ) (k : ℕ) (hk : 1 ≤ k) (hP₂eq : P₂ = RealArchParam.discrete u k hk) :
    ∃ ρ : ℂ, (∀ τ : ℝ, 0 < τ →
        D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (u + (k : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ)))) ∧
      (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0) := by sorry
