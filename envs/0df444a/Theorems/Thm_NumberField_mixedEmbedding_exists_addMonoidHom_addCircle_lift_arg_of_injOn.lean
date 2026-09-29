-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_exists_addMonoidHom_addCircle_lift_arg_of_injOn
-- name    : NumberField.mixedEmbedding.exists_addMonoidHom_addCircle_lift_arg_of_injOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/f585c2c2-d1d1-5e8d-8427-b52a20e659f2
-- title:
--   Circle character on a unit lattice from complex arguments and tilt phases
-- statement:
--   Let $K$ be a number field, $c$ a natural number, and write $r =$ `Fintype.card (InfinitePlace K)` for the number of infinite places of $K$. Let $\mathrm{arg} :$ `mixedSpace K` $\to \mathbb{R}^{\text{nrComplexPlaces } K}$ be any function which is additive modulo integers on units: for all $y, y'$ in the mixed space that are units, there is $k \in \mathbb{Z}^{\text{nrComplexPlaces } K}$ with $\mathrm{arg}(yy') = \mathrm{arg}(y) + \mathrm{arg}(y') + k$. Let $F \le K^\times$ be a subgroup and $L : K^\times \to \mathbb{R}^r \times \mathbb{Z}^c$ a map which is additive on $F$ ($L(\varphi\psi) = L\varphi + L\psi$ for $\varphi, \psi \in F$) and has trivial kernel on $F$ ($L\varphi = 0$ with $\varphi \in F$ forces $\varphi = 1$). Let $\Lambda \le \mathbb{R}^r \times \mathbb{Z}^c$ be an additive subgroup whose elements are exactly the values $L\varphi$ with $\varphi \in F$, and let $b \in \mathbb{R}^c$. Then there exist an additive homomorphism $\chi : \Lambda \to (\mathbb{R}/\mathbb{Z})^{r+c}$ (with `AddCircle (1 : ℝ)` as target in each coordinate) and a function $\mathrm{lift} : \mathbb{R}^r \times \mathbb{Z}^c \to \mathbb{R}^{r+c}$ such that $\mathrm{lift}\,0 = 0$; for every $\gamma \in \Lambda$ and every coordinate $j$, the real number $\mathrm{lift}(\gamma)_j$ reduces modulo $1$ to $\chi(\gamma)_j$; and for every $\varphi \in F$, first, for every complex infinite place $w$ of $K$, the coordinate of $\mathrm{lift}(L\varphi)$ in the slot `Fin.castAdd c` of the index of $w$ among all infinite places reduces modulo $1$ to $\mathrm{arg}(\mathrm{mixedEmbedding}\,K\,\varphi)$ at the index of $w$ among the complex places, and second, for every $j < c$, the coordinate of $\mathrm{lift}(L\varphi)$ in the slot `Fin.natAdd r j` reduces modulo $1$ to $b_j \cdot (L\varphi)_2(j)$. Here the two index families are the enumerations given by `Fintype.equivFin` on the infinite places and on the complex places.
--
--   This is the construction of a circle-valued character on the lattice $\Lambda = L(F)$ together with a real-valued lift of it, the character being prescribed on the complex slots by the argument function on the mixed space and on the remaining $c$ slots by the tilt phases $b_j$ paired with the integral part of $L$. It is used in the analytic lattice-sum estimates for number fields, namely by [`NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le`](thm.html#NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le) and [`NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_window_eq_sum_tsum_ite_of_contDiff_of_isLocallyConstant`](thm.html#NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_window_eq_sum_tsum_ite_of_contDiff_of_isLocallyConstant), where the character appears as the twist of a unit sum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_exists_addMonoidHom_addCircle_lift_arg_of_injOn.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical in

theorem NumberField.mixedEmbedding.exists_addMonoidHom_addCircle_lift_arg_of_injOn
    (K : Type) [Field K] [NumberField K] {c : ℕ}
    (arg : mixedSpace K → (Fin (nrComplexPlaces K) → ℝ))
    (harg : ∀ y y' : mixedSpace K, IsUnit y → IsUnit y' →
      ∃ k : Fin (nrComplexPlaces K) → ℤ, arg (y * y') = arg y + arg y' + fun j => (k j : ℝ))
    (F : Subgroup Kˣ)
    (L : Kˣ → (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin c → ℤ))
    (hL_mul : ∀ φ ∈ F, ∀ ψ ∈ F, L (φ * ψ) = L φ + L ψ)
    (hL_inj : ∀ φ ∈ F, L φ = 0 → φ = 1)
    (Λ : AddSubgroup ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin c → ℤ)))
    (hΛ : ∀ γ, γ ∈ Λ ↔ ∃ φ ∈ F, L φ = γ)
    (b : Fin c → ℝ) :
    ∃ (χ : Λ →+ (Fin (Fintype.card (InfinitePlace K) + c) → AddCircle (1 : ℝ)))
      (lift : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin c → ℤ) →
        (Fin (Fintype.card (InfinitePlace K) + c) → ℝ)),
      lift 0 = 0 ∧
      (∀ (γ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin c → ℤ)) (hγ : γ ∈ Λ)
          (j : Fin (Fintype.card (InfinitePlace K) + c)), ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j) ∧
      ∀ φ ∈ F,
        (∀ w : {w : InfinitePlace K // w.IsComplex},
          ((lift (L φ) (Fin.castAdd c (Fintype.equivFin (InfinitePlace K) w.1)) : ℝ) : AddCircle (1 : ℝ)) =
            ((arg (mixedEmbedding K (φ : K)) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} w) : ℝ) :
              AddCircle (1 : ℝ))) ∧
        (∀ j : Fin c,
          ((lift (L φ) (Fin.natAdd (Fintype.card (InfinitePlace K)) j) : ℝ) : AddCircle (1 : ℝ)) =
            ((b j * ((L φ).2 j : ℝ) : ℝ) : AddCircle (1 : ℝ))) := by sorry
