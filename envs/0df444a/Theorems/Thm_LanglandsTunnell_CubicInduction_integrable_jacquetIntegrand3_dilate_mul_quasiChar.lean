-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_jacquetIntegrand3_dilate_mul_quasiChar
-- name    : LanglandsTunnell.CubicInduction.integrable_jacquetIntegrand3_dilate_mul_quasiChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/9e0d94d0-1fcd-5452-b38f-ee39872cd532
-- title:
--   Joint integrability of the dilated Jacquet integrand in three variables
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ and let $\mu$ be a homomorphism from the ideles of $K$ to $\mathbb{C}^\times$ which is trivial on principal ideles, continuous and of absolute value $1$. Data $uR(w)\in\mathbb{C}$, $aR(w)\in\mathbb{Z}/2$ at the real places and $uC(w)\in\mathbb{C}$, $kC(w)\in\mathbb{Z}$ at the complex places are assumed to describe the archimedean components of $\mu$, in the sense that at each place $w$ and each unit $x$ of $w$'s completion the local character equals $\|x\|^{\mathrm{mult}(w)u}\cdot(\iota_w(x)/\|x\|)^{a}$ with $(u,a)=(uR(w),aR(w)^{\mathrm{val}})$ respectively $(uC(w),kC(w))$; a further character $\omega$ of the ideles of $\mathbb{Q}$ has real archimedean components with exponent $\sum_w uR(w)+\sum_w 2uC(w)$ and integer $\sum_w aR(w)^{\mathrm{val}}+\sum_w (kC(w)+1)$, and $E$ splits the infinite part of the ideles of $\mathbb{Q}$ (infinite part $u$, finite part $1$). Further: a nonzero rational $a$ together with a unit $a_\infty$ of the infinite adeles over it; $\psi_\infty(x)=\psi_{\mathrm{arch}}(a x)$; measures $\nu_{\mathrm{add}}=|a|^{1/2}$ times the transport of Lebesgue measure from the mixed space and a Haar measure $\nu_{\mathrm{mul}}$ on the infinite ideles; these global data are summarised here. Let $w_0$ be a real place of $K$ and $P_2$ a real archimedean parameter for the remaining places: either $K$ has exactly the three distinct real places $w_0,w_1,w_2$ and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$, or $K$ has exactly the places $w_0$ and a complex $w_C$, with $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$ when $kC(w_C)\neq 0$ and $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$ when $kC(w_C)=0$. Let $D$ be a real archimedean Whittaker datum with parameter $P_2$ (a smooth $W$ on $2\times2$ real matrices with the unipotent and central laws, entire twisted zeta functions, functional equation and growth and decay bounds), let $S(M)=p(M)\exp(-\pi\sum_{i,b}M_{ib}^2)$ for a complex polynomial $p$ in the six entries of a real $2\times3$ matrix, and let $c_0$ be a real number such that for each $\alpha\in\mathbb{Z}/2$ every element of the $\Gamma_{\mathbb{R}}$- and $\Gamma_{\mathbb{C}}$-shift multisets of $P_2$ twisted by $(0,\alpha)$ has real part $>-c_0$. The conclusion: for all $t\in\mathbb{C}$, $e\in\mathbb{Z}$, $g_\infty\in \mathrm{GL}_3$ of the infinite adeles of $\mathbb{Q}$ and $s\in\mathbb{C}$ with $\max(c_0,-\mathrm{Re}\,uR(w_0))-\mathrm{Re}\,t<\mathrm{Re}\,s$, the function $$(y,x)\mapsto \mathrm{jacquetIntegrand3}\,D\,uR(w_0)\,aR(w_0)\,(a y)\,\psi_\infty\,S\,g_\infty\,x\cdot |y|^{t}\mathrm{sgn}(y)^{e}\cdot |y|^{s-1}|y|^{-1}$$ on $\mathbb{R}\times(\mathbb{R}^{2\times 2})$ is integrable for the product of Lebesgue measures, where the first factor is the Godement inner integral $\int_{\mathbb{R}^2} S\big(x\cdot[\,m_{0\bullet}+v_0 m_{2\bullet};\,m_{1\bullet}+v_1 m_{2\bullet}\,]\big)\psi_\infty(-v_1)\,dv$ with $m$ the real matrix of $g_\infty$, multiplied by $|\det x|^{uR(w_0)+2}\mathrm{sgn}(\det x)^{aR(w_0)}|\det x|^{-2}$ and by $W\big(\mathrm{diag}(a y,1)\,x^{-1}\big)$.
--
--   This is the joint absolute convergence, in the dilation variable $y$ and the real $2\times2$ array $x$, of the integrand attached to the Jacquet vector of a $\mathrm{GL}_2$ archimedean datum twisted by a quasi-character, valid in the half-plane determined by $c_0$ and the data at the distinguished real place. It is the hypothesis that licenses the interchange of integrations in the unfolding of the archimedean zeta integral of that vector, and is used by [`LanglandsTunnell.CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul`](thm.html#LanglandsTunnell.CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul) and [`LanglandsTunnell.CubicInduction.jacquetVector3_isArchZetaConvergentAbove`](thm.html#LanglandsTunnell.CubicInduction.jacquetVector3_isArchZetaConvergentAbove).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integrable_jacquetIntegrand3_dilate_mul_quasiChar.lean

import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.integrable_jacquetIntegrand3_dilate_mul_quasiChar
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
      (∀ μ ∈ (P₂.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P₂.twist 0 a).gammaC, -ν.re < c₀)) :
    ∀ (t : ℂ) (e : ℤ) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ),
      max c₀ (-(uR w₀ h₀).re) - t.re < s.re →
      MeasureTheory.Integrable
        (fun p : ℝ × (Fin 2 → Fin 2 → ℝ) =>
          jacquetIntegrand3 D (uR w₀ h₀) (aR w₀ h₀) ((a : ℝ) * p.1) psiInf S gInf p.2 *
            ArchR.quasiChar t (e : ZMod 2) p.1 * ((|p.1| : ℝ) : ℂ) ^ (s - 1) * ((|p.1| : ℝ) : ℂ)⁻¹)
        (MeasureTheory.volume.prod MeasureTheory.volume) := by sorry
