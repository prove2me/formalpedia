-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_archZeta30_jacquetVector3_eq_archFactor_mul
-- name    : LanglandsTunnell.CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/0dd50e37-0d88-5401-8260-50c783f22dd1
-- title:
--   Archimedean zeta integral of `jacquetVector3`, unfolded
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ and let $\mu$ be a character of the ideles of $K$ which is trivial on principal ideles, continuous and of absolute value $1$; its archimedean component at each real place $w$ is $x\mapsto \|x\|^{\mathrm{mult}_w\,u_R(w)}\,\mathrm{sgn}(x)^{a_R(w)}$ (with $a_R(w)\in\mathbb{Z}/2$ read as an integer) and at each complex place $x\mapsto\|x\|^{\mathrm{mult}_w\,u_C(w)}(x/\|x\|)^{k_C(w)}$, in the sense of `IsArchCompAt`. Let $\omega$ be a character of the ideles of $\mathbb{Q}$ whose real archimedean component has exponent $\sum_w u_R(w)+\sum_w 2u_C(w)$ and sign exponent $\sum_w a_R(w)+\sum_w (k_C(w)+1)$. Let $E$ be a monoid map from the infinite idele units to the idele units with infinite part the identity and finite part $1$; let $a\in\mathbb{Q}^\times$ with a unit $a_\infty$ lying over it, and $\psi_\infty(x)=\psi_{\mathrm{arch}}(ax)$. Fix measurable and Borel structures on the infinite adeles and their units, a measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the transport of Lebesgue measure along the mixed-space identification, and a Haar measure $\nu_{\mathrm{mul}}$ on the infinite idele units. Let $w_0$ be a real place of $K$ and $P_2$ a real archimedean parameter which, according to whether $K$ has three real places or one real and one complex place, is the principal parameter built from the two other real places, or `discrete` of weight $|k_C(w_C)|$ when $k_C(w_C)\neq0$, or `principal` $(u_C(w_C),0,u_C(w_C),1)$ when $k_C(w_C)=0$. Let $D$ be an `ArchDatumR` for $P_2$, let $S$ be a polynomial multiple of the Gaussian on real $2\times3$ matrices, let $c_0$ be a real number with $-\operatorname{Re}\mu<c_0$ for every shift $\mu$ in the $\Gamma_{\mathbb{R}}$-multiset and $\Gamma_{\mathbb{C}}$-multiset of $P_2$ twisted by $(0,a)$ for both $a\in\mathbb{Z}/2$, and let $\kappa$ be a real number such that the image of $\nu_{\mathrm{mul}}$ under the real coordinate is $\kappa\,dy/|y|$. Then for every character $\sigma$ of the ideles of $\mathbb{Q}$ that is trivial on principal ideles, continuous and unitary, with real archimedean component of exponent $t$ and sign exponent $e$, every $g_\infty\in \mathrm{GL}_3$ of the infinite adeles, and every $s$ with $\max(c_0,-\operatorname{Re}u_R(w_0))-\operatorname{Re}t<\operatorname{Re}s$ and $D.\mathrm{zeta\_abscissa}<\operatorname{Re}s+\operatorname{Re}t$, the integral `archZeta30` of the right translate $h\mapsto \mathrm{jacquetVector3}\,D\,u_R(w_0)\,a_R(w_0)\,a\,\psi_\infty\,S\,(h\,g_\infty)$ against $\sigma\circ E$ at $s$ and at the identity equals $\kappa$ times the archimedean $\Gamma$-factor of $P_2$ twisted by $(t,e\bmod 2)$ at $s$, times $\mathrm{quasiChar}(u_R(w_0)+1,a_R(w_0))$ of $\det$ of the real matrix of $g_\infty$, times the integral over real $2\times2$ matrices $x$ of $\mathrm{godementInner3}\,\psi_\infty\,S\,x$ at that real matrix, times $\mathrm{quasiChar}(u_R(w_0)+2,a_R(w_0))(\det x)$, times $|\det x|^{-2}$, times $D.\mathrm{zetaEntire}$ at $\mathrm{diagOne}(a)\,x^{-1}$, $t$, $e\bmod 2$ and $s$.
--
--   This is the archimedean unfolding step for the $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integral of the Godement-type vector built from a $\mathrm{GL}_2$ Whittaker datum: the torus variable of the zeta integral re-dilates the vector, and exchanging the order of integration replaces the inner variable by the datum's own twisted zeta integral, evaluated through its $\Gamma$-factor and entire part. It feeds [`LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package`](thm.html#LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package), the archimedean input to the converse-theorem construction for cubic fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_archZeta30_jacquetVector3_eq_archFactor_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul
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
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹) :
    ∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
      ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
      ∀ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ),
        max c₀ (-(uR w₀ h₀).re) - t.re < s.re → D.zeta_abscissa < s.re + t.re →
        archZeta30 ν_mul (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf))
            (σ.comp E) s 1 =
          (κ : ℂ) * (P₂.twist t (e : ZMod 2)).archFactor s *
            (ArchR.quasiChar (uR w₀ h₀ + 1) (aR w₀ h₀) (StandardKernel.realMat gInf).det *
              ∫ x : Fin 2 → Fin 2 → ℝ,
                godementInner3 psiInf S (Matrix.of x) (StandardKernel.realMat gInf) *
                  ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of x).det *
                    (((|(Matrix.of x).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                  D.zetaEntire (ArchR.diagOne (a : ℝ) * (Matrix.of x)⁻¹) t (e : ZMod 2) s) := by sorry
