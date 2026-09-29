-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_scalar_mul
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_scalar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/cc4e20dc-651f-520f-853d-ff618019ec8b
-- title:
--   Central character of the explicit GL₃ Jacquet vector
-- statement:
--   Let $K$ be a number field, equipped with a complex number $u_R(w)$ and a parity $a_R(w)\in\mathbb{Z}/2$ for each real place $w$, and a complex number $u_C(w)$ and an integer $k_C(w)$ for each complex place. Let $\omega$ be a homomorphism from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$ which satisfies `IsArchCompAt` at every real place $v$ of $\mathbb{Q}$ with exponent $u=\sum_{w\ \mathrm{real}}u_R(w)+\sum_{w\ \mathrm{complex}}2u_C(w)$ and integer $a=\sum_{w\ \mathrm{real}}(a_R(w)).\mathrm{val}+\sum_{w\ \mathrm{complex}}(k_C(w)+1)$ (finite sums over the places), i.e. the local character of $\omega$ at $v$ sends a unit $x$ of the completion to $\|x\|^{\,\mathrm{mult}(v)\,u}\,(x/\|x\|)^{a}$ under the chosen embedding. Let $E$ be a homomorphism from the units of the infinite adeles of $\mathbb{Q}$ to the ideles of $\mathbb{Q}$ whose infinite part is the identity and whose finite part is trivial. Fix $a\in\mathbb{Q}$, an additive character $\psi_\infty$ of the infinite adeles, a real place $w_0$ of $K$, a parameter $P_2$ of type `RealArchParam`, a datum $D$ of type `ArchDatumR P₂` and a function $S$ on real $2\times 3$ matrices. Assume that either $K$ has exactly three places, $w_0$ and two further distinct real places $w_1,w_2$, with $P_2$ the principal parameter built from $(u_R(w_1),a_R(w_1))$ and $(u_R(w_2),a_R(w_2))$; or $K$ has exactly the two places $w_0$ and a complex place $w_C$, with $P_2$ the discrete parameter of weight $|k_C(w_C)|$ and exponent $u_C(w_C)$ when $k_C(w_C)\neq0$, and the principal parameter built from $(u_C(w_C),0)$ and $(u_C(w_C),1)$ when $k_C(w_C)=0$. Then for every unit $z$ of the infinite adeles of $\mathbb{Q}$ and every $g\in\mathrm{GL}_3$ of the infinite adeles, the vector $\mathtt{jacquetVector3}\,D\,(u_R(w_0))\,(a_R(w_0))\,a\,\psi_\infty\,S$ evaluated at the scalar matrix of $z$ times $g$ equals $\omega(E(z))$ times its value at $g$.
--
--   This is the central-character transformation law of the explicit Jacquet–Whittaker vector on $\mathrm{GL}_3$ over the archimedean adeles: the centre acts through the global character $\omega$, read off via the section $E$ of the infinite part of the ideles. It is one of the properties assembled into the archimedean zeta-integral package for this vector, and it is also used in the estimate for the norm of its third archimedean component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_scalar_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField LanglandsTunnell.Converse
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.jacquetVector3_scalar_mul
    (K : Type) [Field K] [NumberField K]
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    :
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g)
            = ((ω (E z) : ℂˣ) : ℂ) * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) g) := by sorry
