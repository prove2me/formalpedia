-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isKFinite_jacquetVector3
-- name    : LanglandsTunnell.CubicInduction.isKFinite_jacquetVector3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/2212a938-94fe-5cdd-b06e-90b4b9d1d2a0
-- title:
--   K-finiteness of the polynomial-times-Gaussian Jacquet vector on GL₃
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ and let $\mu$ be a character of the ideles $(\mathbb{A}_K)^\times$ into $\mathbb{C}^\times$ that is an admissible twist, i.e. trivial on $K^\times$, continuous and of absolute value $1$ everywhere. Assume given complex exponents $uR$ and signs $aR \in \mathbb{Z}/2$ at the real places of $K$, complex exponents $uC$ and integers $kC$ at the complex places, such that at each place $w$ the archimedean local component of $\mu$ is $x \mapsto \|x\|^{\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$ with the corresponding data; and a character $\omega$ of $(\mathbb{A}_{\mathbb{Q}})^\times$ whose archimedean component at each real place of $\mathbb{Q}$ is described by the same formula with exponent $\sum_w uR_w + \sum_w 2\,uC_w$ and integer $\sum_w aR_w + \sum_w (kC_w+1)$. Assume further a homomorphism $E$ splitting the infinite ideles of $\mathbb{Q}$ into the full ideles with infinite part the identity and finite part $1$; a nonzero rational $a$ together with a unit $aInf$ of the infinite adeles representing it; the additive character $\psi_\infty(x) = \mathrm{psiArch}(a\,x)$; measurable and Borel structures on the infinite adeles of $\mathbb{Q}$ and their units, an additive measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the pushforward of Lebesgue measure along the mixed-space identification, and a Haar measure $\nu_{\mathrm{mul}}$ on the units. Let $w_0$ be a real place of $K$ and let $P_2$ be a real archimedean parameter satisfying: either $K$ has exactly the three distinct real places $w_0,w_1,w_2$ and $P_2$ is the principal parameter built from $(uR_{w_1},aR_{w_1})$ and $(uR_{w_2},aR_{w_2})$, or $K$ has exactly the places $w_0$ and one complex place $w_C$, and $P_2$ is the discrete parameter with data $uC_{w_C}$ and weight $|kC_{w_C}|$ when $kC_{w_C} \neq 0$, respectively the principal parameter with data $(uC_{w_C},0)$, $(uC_{w_C},1)$ when $kC_{w_C}=0$. Finally let $D$ be an archimedean Whittaker datum for $P_2$ (a function $W$ on $2\times 2$ real matrices with the prescribed smoothness, unipotent and central transformation laws, entire zeta functions with functional equation and finite order, and decay conditions), and let $S$ be a section of the form $M \mapsto p(M_{ij})\,\mathrm{gaussian3}(M)$ for some polynomial $p$ in the six entries with complex coefficients. Then the vector $g \mapsto \mathrm{quasiChar}(uR_{w_0}+1, aR_{w_0})(\det g_{\mathrm{real}}) \cdot \int_{e} \mathrm{jacquetIntegrand3}\,D\,uR_{w_0}\,aR_{w_0}\,a\,\psi_\infty\,S\,g\,e$ on $\mathrm{GL}_3$ of the infinite adeles of $\mathbb{Q}$ is $K$-finite: there is a finite set of complex-valued functions on $\mathrm{GL}_3$ of the infinite adeles whose $\mathbb{C}$-span contains every right translate $x \mapsto J(xk)$ with $k$ in $\mathrm{orth3}$.
--
--   This is the archimedean $K$-finiteness of the explicit Whittaker vector attached to a polynomial-times-Gaussian Schwartz section, one of the conditions required of the archimedean component in the converse theorem for $\mathrm{GL}_3$ used in the cubic induction step. It is assembled, together with the integrability and continuity statement it cites, into [`LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package`](thm.html#LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isKFinite_jacquetVector3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.isKFinite_jacquetVector3
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
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) :
    IsKFinite (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) := by sorry
