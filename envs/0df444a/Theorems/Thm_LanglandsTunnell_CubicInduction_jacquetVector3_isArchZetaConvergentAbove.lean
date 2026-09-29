-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_isArchZetaConvergentAbove
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/5f2bce7b-6965-5a2c-8a36-0bee3702e474
-- title:
--   Convergence half-planes for archimedean GL₃timesGL₁ zeta integrals
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ and let $\mu$ be a character of the ideles of $K$ which is trivial on $K^\times$, continuous and unitary. Attached to $\mu$ are complex exponents $u_w$ and signs $a_w\in\mathbb{Z}/2$ at the real places, and exponents $u_w$ and integers $k_w$ at the complex places, in the sense that the archimedean local component of $\mu$ at $w$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,u_w}\,(x/\|x\|)^{a_w}$, respectively with exponent $k_w$; $\omega$ is a character of the ideles of $\mathbb{Q}$ whose component at the real place has exponent $\sum_w u_w+\sum_w 2u_w$ and integer parameter $\sum_w a_w+\sum_w(k_w+1)$. Further data: a multiplicative section $E$ of the infinite part of the ideles of $\mathbb{Q}$ with trivial finite part; a nonzero rational $a$, a unit $a_\infty$ of the infinite adeles equal to the image of $a$, and the additive character $\psi_\infty(x)=\psi_{\mathrm{arch}}(ax)$; Borel measurable structures, the measure $\nu^+=|a|^{1/2}$ times the transport of Lebesgue measure on the mixed space, and a Haar measure $\nu^\times$ on the units of the infinite adeles; a real place $w_0$ of $K$ and a parameter $P_2$ which is either $\mathrm{principal}(u_{w_1},a_{w_1},u_{w_2},a_{w_2})$ when $K$ has exactly the three real places $w_0,w_1,w_2$, or, when $K$ has exactly one complex place $w_C$ besides $w_0$, $\mathrm{discrete}(u_{w_C},|k_{w_C}|)$ if $k_{w_C}\neq0$ and $\mathrm{principal}(u_{w_C},0,u_{w_C},1)$ if $k_{w_C}=0$; a real archimedean Whittaker datum $D$ for $P_2$ (a function on $2\times2$ real matrices, smooth on the invertible locus, with the unipotent and central transformation laws, entire zeta functions satisfying the functional equation and the growth and decay estimates); a function $S$ on $2\times3$ real matrices of the form polynomial times Gaussian; and reals $c_0$, $c_1$ with $-\operatorname{Re}\gamma<c_0$ for every gamma-exponent $\gamma$ of both sign twists $P_2.\mathrm{twist}\,0\,a$, and $-\operatorname{Re}\gamma<c_1$ for the corresponding twists of $P_2.\mathrm{dual}$. Then for every character $\sigma$ of the ideles of $\mathbb{Q}$ which is trivial on $\mathbb{Q}^\times$, continuous and unitary, every $t\in\mathbb{C}$ and $e\in\mathbb{Z}$ such that the real archimedean component of $\sigma$ has exponent $t$ and parameter $e$, and every $g_\infty\in\mathrm{GL}_3$ of the infinite adeles, writing $W(h)=\mathrm{jacquetVector3}\,D\,u_{w_0}\,a_{w_0}\,a\,\psi_\infty\,S\,(h\,g_\infty)$: for all $s$ with $\operatorname{Re} s>\max(c_0,-\operatorname{Re}u_{w_0})-\operatorname{Re}t$ the function $z\mapsto W(\iota(\mathrm{diag}(z,1)))\,\sigma(E z)\,\|z\|^{s-1}$ is integrable for $\nu^\times$, and for all $s$ with $\operatorname{Re} s>\max(c_1,\operatorname{Re}u_{w_0})+\operatorname{Re}t$ the function $(z,x)\mapsto W(w_3\,{}^{t}(\iota(\mathrm{diag}(z,1))\,n_{21}(x)\,w'_3)^{-1})\,\sigma(E z)^{-1}\,\|z\|^{s-1}$ is integrable for $\nu^\times\times\nu^+$, where $w_3$ is the long Weyl element, $w'_3$ the transposition of the last two coordinates, and $n_{21}(x)$ the lower unipotent matrix in position $(2,1)$.
--
--   This records the abscissae of absolute convergence of the archimedean $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integral of the Jacquet-type Whittaker vector built from a Schwartz section and of its dual integral, uniformly in the admissible twist $\sigma$ and in right translates of the vector. It is the first input to the analytic continuation and functional equation of these integrals, used by [`LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package`](thm.html#LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicLambda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.jacquetVector3_isArchZetaConvergentAbove
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
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P₂.twist 0 a).gammaC, -ν.re < c₀))
    (c₁ : ℝ)
    (hc₁ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.dual.twist 0 a).gammaR, -μ.re < c₁) ∧ (∀ ν ∈ (P₂.dual.twist 0 a).gammaC, -ν.re < c₁)) :
    ∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
      ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
      ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ),
        IsArchZeta30ConvergentAbove ν_mul
            (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf))
            (σ.comp E) 1 (max c₀ (-(uR w₀ h₀).re) - t.re) ∧
        IsArchZeta31ConvergentAbove ν_mul ν_add
            (dualWhittakerFn3
              (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf)))
            (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) (max c₁ (uR w₀ h₀).re + t.re) := by sorry
