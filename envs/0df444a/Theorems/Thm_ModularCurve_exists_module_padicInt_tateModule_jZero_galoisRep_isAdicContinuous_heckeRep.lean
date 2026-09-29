-- Prove2me | Theorems.Thm_ModularCurve_exists_module_padicInt_tateModule_jZero_galoisRep_isAdicContinuous_heckeRep
-- name    : ModularCurve.exists_module_padicInt_tateModule_jZero_galoisRep_isAdicContinuous_heckeRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/ae3cbaa5-73e6-57d6-ab77-e34a8c7d74f3
-- title:
--   Structures on the λ-adic Tate module of J₀(M)
-- statement:
--   Fix $M \ge 1$ and a prime $\lambda$, and equip $J_0(M) := \mathrm{Pic}^0$ of the field [`ModularCurve.modularFunctionFieldBar M`](def/ModularCurve_ArithmeticGalois.html#L111) over $\overline{\mathbb Q}$ (the degree-zero divisors modulo principal ones) with the [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14)-module structure [`ModularCurve.heckeModuleBar M`](def/ModularCurve_HeckeModule.html#L82), i.e. the action of $\mathbb Z[T_\ell : \ell \text{ prime}]$ obtained by evaluating at the divisorial operators `heckeOperatorBar` when these commute and by sending all variables to $0$ otherwise; let $T :=$ [`ModularCurve.TateModule lam (JZero M)`](def/ModularCurve_EichlerShimuraData.html#L15) be the Hecke submodule of sequences $(x_n)_{n\ge 0}$ in $J_0(M)$ with $x_0 = 0$ and $\lambda x_{n+1} = x_n$. The assertion is that there is a $\mathbb Z_\lambda$-module structure on $T$ for which $a \in \mathbb Z_\lambda$ acts on the $n$-th component of $x$ by the natural number underlying the image of $a$ in $\mathbb Z/\lambda^n$, that for this structure $T$ is a finitely generated free $\mathbb Z_\lambda$-module, and that for every commutative local ring $\mathcal O''$ which is a $\mathbb Z_\lambda$-algebra and in which the image of $\lambda$ lies in the maximal ideal there exist a monoid homomorphism $\rho_M$ from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to the $\mathcal O''$-linear endomorphisms of $\mathcal O'' \otimes_{\mathbb Z_\lambda} T$ and a ring homomorphism $T_M$ from [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14) to the same endomorphism ring such that: whenever $\sigma$ carries the sequence $x$ to the sequence $y$ componentwise, $\rho_M(\sigma)(a \otimes x) = a \otimes y$ for all $a \in \mathcal O''$; $\rho_M$ satisfies [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9), meaning that for each $n$ there is a finite-dimensional intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$ with $\rho_M(\sigma)v - v \in \mathfrak m_{\mathcal O''}^n \cdot (\mathcal O'' \otimes T)$ for every $\sigma$ fixing $L$ pointwise and every $v$; and $T_M(t)(a \otimes x) = a \otimes (t \cdot x)$ for all $t$, $a$, $x$.
--
--   This records the existence of the structures — a $\mathbb Z_\lambda$-module structure with the expected componentwise scalar action, finiteness and freeness, and, after base change to a local $\mathbb Z_\lambda$-algebra, commuting adically continuous Galois and Hecke actions — over which the Eichler–Shimura eigenplane statements for $T_\lambda(J_0(M))$ are quantified, so that those statements may be specialised. It is used in the construction of the $\lambda$-adic representations attached to a newform together with an ordinary line, in the forms [`CuspForm.IsNewform.exists_galoisRepAdic_ordinaryLine_frobenius_sub_qCoeff_smul_mem_of_dvd_of_not_sq_dvd`](thm.html#CuspForm.IsNewform.exists_galoisRepAdic_ordinaryLine_frobenius_sub_qCoeff_smul_mem_of_dvd_of_not_sq_dvd) and [`CuspForm.IsNewform.exists_galoisRepAdic_ordinaryLine_frobenius_sub_unitRoot_smul_mem_of_not_dvd`](thm.html#CuspForm.IsNewform.exists_galoisRepAdic_ordinaryLine_frobenius_sub_unitRoot_smul_mem_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_module_padicInt_tateModule_jZero_galoisRep_isAdicContinuous_heckeRep.lean

import Definitions.Def_GaloisRep_Adic
import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.TensorProduct.Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve TensorProduct

theorem ModularCurve.exists_module_padicInt_tateModule_jZero_galoisRep_isAdicContinuous_heckeRep
    (M : ℕ) [NeZero M] (lam : ℕ) [Fact lam.Prime] :
    letI := ModularCurve.heckeModuleBar M
    ∃ (_ : Module ℤ_[lam] (ModularCurve.TateModule lam (JZero M))),
      (∀ (a : ℤ_[lam]) (x : ModularCurve.TateModule lam (JZero M)) (n : ℕ),
        ((a • x : ModularCurve.TateModule lam (JZero M)) : ℕ → JZero M) n =
          (PadicInt.toZModPow n a).val • (x : ℕ → JZero M) n) ∧
      Module.Finite ℤ_[lam] (ModularCurve.TateModule lam (JZero M)) ∧
      Module.Free ℤ_[lam] (ModularCurve.TateModule lam (JZero M)) ∧
      ∀ (O'' : Type) [CommRing O''] [IsLocalRing O''] [Algebra ℤ_[lam] O''],
        (lam : O'') ∈ IsLocalRing.maximalIdeal O'' →
        ∃ (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
              Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (JZero M)))
          (TM : ModularCurve.HeckeAlg →+*
              Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (JZero M))),
          (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
              (x y : ModularCurve.TateModule lam (JZero M)),
            (y : ℕ → JZero M) = σ • (x : ℕ → JZero M) →
              ∀ a : O'', ρM σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] y) ∧
          GaloisActionIsAdicContinuous O'' ρM ∧
          (∀ (t : ModularCurve.HeckeAlg) (a : O'') (x : ModularCurve.TateModule lam (JZero M)),
            TM t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] (t • x)) := by sorry
