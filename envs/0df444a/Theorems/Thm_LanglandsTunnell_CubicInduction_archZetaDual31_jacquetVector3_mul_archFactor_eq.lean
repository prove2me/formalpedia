-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_archZetaDual31_jacquetVector3_mul_archFactor_eq
-- name    : LanglandsTunnell.CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/c1deee73-0875-5c86-b2e0-a1f470b3fc16
-- title:
--   Archimedean functional equation for the induced GL₃ zeta integrals
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ and let $\mu$ be a character of the idele units of $K$ that is trivial on principal ideles, continuous and of absolute value $1$; let $uR,aR$ assign to each real place $w$ a complex number and a class in $\mathbb{Z}/2$, and $uC,kC$ to each complex place a complex number and an integer, such that for every place the archimedean component of $\mu$ at $w$ is $x\mapsto \|x\|^{m_w u}\,(x/\|x\|)^{a}$ with $u,a$ the assigned data ($a=(aR\,w)$ lifted to $\mathbb{Z}$ at real places). Let $\omega$ be a character of the idele units of $\mathbb{Q}$ whose component at the real place has exponent $\sum_w uR\,w+\sum_w 2\,uC\,w$ and integer parameter $\sum_w (aR\,w)+\sum_w (kC\,w+1)$, and let $E$ be a homomorphism from the infinite idele units of $\mathbb{Q}$ to the idele units splitting the infinite part and having finite part $1$. Let $a\in\mathbb{Q}^{\times}$, $a_\infty$ the corresponding infinite idele, $\psi_\infty(x)=\psi_{\mathrm{arch}}(ax)$, $\nu_{\mathrm{add}}=|a|^{1/2}$ times Lebesgue measure transported to the infinite adeles, and $\nu_{\mathrm{mul}}$ a Haar measure on the infinite idele units (with the relevant measurability and Borel assumptions). Fix a real place $w_0$ of $K$ and a real archimedean parameter $P_2$ which is either $\mathrm{principal}(uR\,w_1,aR\,w_1,uR\,w_2,aR\,w_2)$ for the two remaining real places $w_1\neq w_2$ when all infinite places are $\{w_0,w_1,w_2\}$, or, when the infinite places are $\{w_C,w_0\}$ with $w_C$ complex, $\mathrm{discrete}(uC\,w_C,|kC\,w_C|)$ if $kC\,w_C\neq 0$ and $\mathrm{principal}(uC\,w_C,0,uC\,w_C,1)$ if $kC\,w_C=0$. Let $D$ be a real $GL_2$ Whittaker datum of parameter $P_2$, let $S$ be a polynomial multiple of the Gaussian on real $2\times 3$ matrices, and let $c_0$, $c_1$ be reals strictly exceeding $-\mathrm{Re}$ of every Gamma shift of $P_2$, resp. of its dual, twisted by $(0,a)$ for both parities. The assertion is: for every character $\sigma$ of the idele units of $\mathbb{Q}$ that is trivial on principal ideles, continuous and unitary, every $t\in\mathbb{C}$ and $e\in\mathbb{Z}$ realising the archimedean component of $\sigma$ at the real place, every $g_\infty\in GL_3$ of the infinite adeles and every $s$ with $\max(c_0,-\mathrm{Re}\,uR\,w_0)-\mathrm{Re}\,t<\mathrm{Re}\,s$ and $\max(c_1,\mathrm{Re}\,uR\,w_0)+\mathrm{Re}\,t<\mathrm{Re}(1-s)$, writing $J$ for the Jacquet vector `jacquetVector3` attached to $(D,uR\,w_0,aR\,w_0,a,\psi_\infty,S)$ and right-translated by $g_\infty$, one has $$\mathrm{archZetaDual31}(1-s)\cdot \Gamma\text{-factor}(s)=C\cdot \omega(E a_\infty)\,\sigma(E a_\infty)^3\,|a|^{3(s-1/2)}\cdot\mathrm{archZeta30}(s)\cdot\Gamma\text{-factor}^{\vee}(1-s),$$ where both zeta integrals are formed from $J$ and the character $\sigma\circ E$ at the identity element of $GL_3$, the two Gamma factors are `archFactor` at $s$ and `archFactorDual` at $1-s$ of the L-datum `heckeDatum` of $K$ and $\mu$ with data twisted to $(uR+t,\ aR+e,\ uC+t,\ kC)$, and the constant $C$ is the product over the real places of $\mathrm{signEpsilon}(aR\,w+e)$ (that is, $1$ if $aR\,w+e=0$ and $i$ otherwise), the product over the complex places of $i^{|kC\,w|}$, and $\prod_w \mathrm{lambdaArch}\,w$ ($1$ at real places, $i$ at complex places).
--
--   This is the local functional equation at the archimedean place for the $GL_3\times GL_1$ zeta integrals of Jacquet, Piatetski-Shapiro and Shalika, applied to the explicit Whittaker vector induced from a real $GL_2$ datum and a character at the distinguished real place $w_0$, with the archimedean Euler factors of the cubic field written in the shape produced by `heckeDatum`. It feeds the packaging result [`LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package`](thm.html#LanglandsTunnell.CubicInduction.jacquetVector3_archZeta_package), where it supplies the archimedean half of the functional equation used in the converse-theorem argument for the automorphic induction from the cubic field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_archZetaDual31_jacquetVector3_mul_archFactor_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.archZetaDual31_jacquetVector3_mul_archFactor_eq
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
      ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∀ s : ℂ,
        max c₀ (-(uR w₀ h₀).re) - t.re < s.re → max c₁ (uR w₀ h₀).re + t.re < (1 - s).re →
          archZetaDual31 ν_mul ν_add (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf))
                (σ.comp E) (1 - s) 1 *
              (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s =
            (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
              ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                  fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
              ∏ w : InfinitePlace K, lambdaArch K w) *
            (((ω (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
            (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
            archZeta30 ν_mul (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf))
                (σ.comp E) s 1 *
              (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                  (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual
                (1 - s) := by sorry
