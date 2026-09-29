-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_norm_archComponent3_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/3d0363ff-235f-5e46-9906-db79117c01ed
-- title:
--   Rapid decay of the GL₃ Jacquet–Whittaker vector
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ and let $\mu$ be a character of the idele units of $K$ which is an admissible twist, i.e. trivial on the principal ideles, continuous and unitary. Let $uR,aR$ assign to each real place of $K$ a complex number and an element of $\mathbb{Z}/2$, and $uC,kC$ assign to each complex place a complex number and an integer, such that at every real place $w$ the archimedean local component of $\mu$ is $x\mapsto \|x\|^{\,\mathrm{mult}(w)\,uR(w)}\,(x/\|x\|)^{aR(w)}$ and likewise at every complex place with $uC,kC$. Let $\omega$ be a character of the idele units of $\mathbb{Q}$ whose archimedean component at every real place has exponents $\sum_w uR(w)+\sum_w 2\,uC(w)$ and $\sum_w aR(w)+\sum_w (kC(w)+1)$, and let $E$ split the infinite part, sending each infinite-adelic unit $u$ to an idele with infinite part $u$ and finite part $1$. Let $a\in\mathbb{Q}$, $a\neq 0$, with $a_\infty$ its image among the infinite-adelic units, and let $\psi_\infty(x)=\psi_{\mathrm{arch}}(ax)$. Fix Borel measurable structures on the infinite adeles and their units, an additive measure equal to $|a|^{1/2}$ times the pullback of Lebesgue measure along the mixed-space identification, and a Haar measure on the units. Fix a real place $w_0$ of $K$ and a parameter $P_2$ which either, when $K$ has three real places $w_0,w_1,w_2$, is the principal parameter built from $(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$, or, when the places of $K$ are a complex place $w_C$ and $w_0$, is the discrete parameter with weight $|kC(w_C)|$ when $kC(w_C)\neq 0$ and the principal parameter $(uC(w_C),0,uC(w_C),1)$ when $kC(w_C)=0$. Let $D$ be a real archimedean Whittaker datum for $P_2$ (a function on $2\times 2$ real matrices with the unipotent and central transformation laws, smooth on the invertible locus, with entire zeta functions of finite order satisfying the functional equation and with the stated decay), and let $S$ be a polynomial times the Gaussian on $2\times 3$ real matrices. Then there is $t\in\mathbb{N}$ such that for every $N\in\mathbb{N}$ there is a constant $C$ with $$\big\|\,\mathrm{jacquetVector3}\,D\,(uR(w_0))\,(aR(w_0))\,a\,\psi_\infty\,S\,(g_\infty)\big\| \le \frac{C}{\big(\prod_{v}\mathrm{archRoot}_1(v,g)\,\mathrm{archRoot}_2(v,g)\big)^{t}\,(1+\mathrm{archRootSum}(g))^{N}}$$ for every $g\in \mathrm{GL}_3$ of the adeles of $\mathbb{Q}$, where $g_\infty$ is the archimedean component of $g$, the product runs over the infinite places $v$ of $\mathbb{Q}$, and $\mathrm{archRootSum}(g)=\sum_v(\mathrm{archRoot}_1(v,g)+\mathrm{archRoot}_2(v,g))$.
--
--   This is the archimedean rapid-decay estimate for the $\mathrm{GL}_3$ Whittaker vector obtained by inducing a real $\mathrm{GL}_2$ Whittaker datum against a polynomial-times-Gaussian Schwartz function, the decay being measured in the two root sizes of the archimedean component; since the root sizes are invariant under the centre and the upper unipotent group, the bound is effectively a statement on the torus. It feeds the convergence and contour-shift arguments of [`LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package`](thm.html#LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package), which assembles the archimedean zeta integrals needed for the converse theorem in the cubic induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_norm_archComponent3_le.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.jacquetVector3_norm_archComponent3_le
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
    ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖(jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N) := by sorry
