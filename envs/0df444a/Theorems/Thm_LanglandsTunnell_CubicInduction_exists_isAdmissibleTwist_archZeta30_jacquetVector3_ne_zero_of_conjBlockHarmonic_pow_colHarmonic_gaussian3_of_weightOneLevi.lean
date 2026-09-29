-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightOneLevi
-- name    : LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightOneLevi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/f380e6dd-0904-5eb9-a292-cb8a02a0cf14
-- title:
--   Weight-one Levi branch: non-vanishing archimedean zeta of a Jacquet vector
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$, and let $\mu$ be a character of the idele units of $K$ which is an admissible twist (trivial on principal ideles, continuous, and of absolute value $1$); its archimedean local components are prescribed by data $uR,aR$ at the real places and $uC,kC$ at the complex places in the sense of `IsArchCompAt`, and $\omega$ is a character of the ideles of $\mathbb{Q}$ whose components at the real places of $\mathbb{Q}$ are given by the sums $\sum uR+\sum 2uC$ and $\sum aR+\sum(kC+1)$. Further data: a monoid section $E$ of the infinite ideles into the full ideles of $\mathbb{Q}$ (infinite part $u$, finite part $1$), a nonzero $a\in\mathbb{Q}$ together with the corresponding infinite idele $aInf$, the additive character $\psi_\infty=\psi_{\mathrm{arch}}(a\,\cdot)$, the scaled pushforward measure $\nu_{\mathrm{add}}=|a|^{1/2}\cdot$(volume transported along `InfiniteAdeleRing.ringEquiv_mixedSpace`), and a Haar measure $\nu_{\mathrm{mul}}$ on the infinite idele units. Let $w_0$ be a real place of $K$ and $P_2$ a real archimedean parameter arising, according to `hP₂`, either from two further real places $w_1\neq w_2$ exhausting the places of $K$ together with $w_0$, as $\mathrm{principal}(uR\,w_1,aR\,w_1,uR\,w_2,aR\,w_2)$, or from a complex place $wC$ with $\{wC,w_0\}$ exhausting the places, as $\mathrm{discrete}(uC\,wC,|kC\,wC|)$ when $kC\,wC\neq 0$ and as $\mathrm{principal}(uC\,wC,0,uC\,wC,1)$ when $kC\,wC=0$. Let $D$ be an archimedean Whittaker datum for $P_2$ (a smooth function $W$ on $2\times2$ real matrices satisfying the unipotent and central transformation laws, with entire completed zeta functions, functional equation, finite order and the stated decay), whose $W$ transforms on the right under the row-isometry subgroup by the weight character $\mathrm{archWeightChar}_{\mathbb{R}}$ of $k_0\in\mathbb{Z}$, is a Casimir eigenfunction with eigenvalue $P_2.\mathrm{laplaceEigenvalue}$ on invertible matrices, and is not identically zero; $k_0$ is subject to the minimality conditions $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \pmod 2$ in the principal case and $k_0=m+1$ in the discrete case. Let $m\ge1$, $n\in\mathbb{N}$ and $\varepsilon'\in\mathbb{R}$ with $(\varepsilon',n)=(-1,k_0-m)$ or $(1,m-k_0)$, and let $S$ be the section $S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^m\,(M_{02}+\varepsilon' i M_{12})^n\,e^{-\pi\sum_{i,b}M_{ib}^2}$ on $2\times3$ real matrices. Assume in addition the branch hypotheses $k_0=1$, $P_2=\mathrm{principal}(\mu_1,c_1,\mu_2,c_2)$ with $c_1\neq c_2$, and a constant $\rho\neq0$ such that for every $b\in\mathbb{Z}/2$ and every $\tau>0$ the combination $W(\mathrm{diag}(\tau,1))+(-1)^{b}W(\mathrm{diag}(-\tau,1))$ equals $\rho\,\tau$ times $4\int_0^\infty r^{\mu_1+\mathrm{signShift}(c_1+b)}e^{-\pi r^2}(\tau/r)^{\mu_2+\mathrm{signShift}(c_2+b)}e^{-\pi(\tau/r)^2}\,\frac{dr}{r}$. Then there exist an admissible twist $\sigma$ of the ideles of $\mathbb{Q}$ and an $s\in\mathbb{C}$ such that the archimedean $GL_3\times GL_1$ zeta integral $\int (\,\mathrm{jacquetVector3}\,D\,(uR\,w_0)\,(aR\,w_0)\,a\,\psi_\infty\,S)\bigl(\iota(\mathrm{diag}(y,1))\bigr)\,\sigma(E\,y)\,\|y\|^{s-1}\,d\nu_{\mathrm{mul}}(y)$, evaluated at the identity of $GL_3$, is nonzero.
--
--   This is the weight-one principal-series branch, with the two sheets of the Whittaker function given by the stated Gaussian torus transform, of the archimedean non-vanishing input for the degree-$m$ flat section: it produces a twist of $\mathbb{Q}$ for which the $GL_3\times GL_1$ archimedean zeta integral of the Jacquet vector attached to $S$ does not vanish identically. It feeds the branch-free statement [`LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3), used in the converse-theorem step that realises the cubic induction for Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightOneLevi.lean

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

theorem LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightOneLevi
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
    (m : ℕ) (hm : 1 ≤ m)
    (n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)

    (hk₀ : k₀ = 1) (μ₁ μ₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal μ₁ c₁ μ₂ c₂) (hc : c₁ ≠ c₂) (ρ : ℂ)
    (hD : ∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hρ0 : ρ ≠ 0) :
    ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
      ∃ s : ℂ, archZeta30 ν_mul (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (σ.comp E) s 1 ≠ 0 := by sorry
