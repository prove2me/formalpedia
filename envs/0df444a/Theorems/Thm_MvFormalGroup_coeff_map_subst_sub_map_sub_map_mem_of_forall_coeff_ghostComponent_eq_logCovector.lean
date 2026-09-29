-- Prove2me | Theorems.Thm_MvFormalGroup_coeff_map_subst_sub_map_sub_map_mem_of_forall_coeff_ghostComponent_eq_logCovector
-- name    : MvFormalGroup.coeff_map_subst_sub_map_sub_map_mem_of_forall_coeff_ghostComponent_eq_logCovector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/3f912f9d-875d-56c5-8c1f-63c273efd8fa
-- title:
--   Additivity defect of the truncated logarithm covector
-- statement:
--   Let $\mathcal O$ be a commutative ring, $p$ a prime such that $p$ is a non-zero-divisor in $\mathcal O$, and suppose $\mathbb Z/p$ is an $\mathcal O$-algebra whose structure map has kernel exactly the ideal $(p)$. Let $F$ be a $d$-dimensional formal group law over $\mathcal O$, i.e. a $d$-tuple $F_i \in \mathcal O[[X_1,\dots,X_d,Y_1,\dots,Y_d]]$ with zero constant term, $\mathrm{coeff}_{X_j}F_i=\mathrm{coeff}_{Y_j}F_i=\delta_{ij}$, and the associativity identity between the two triple substitutions, assumed commutative (invariant under interchanging the two blocks of variables). Let $F_p$ be a $d$-tuple of series in the same $2d$ variables with zero constant terms satisfying $\mathrm{coeff}_m(F_{p,i})\cdot p = p^{\deg m}\,\mathrm{coeff}_m(F_i)$ for all $m \neq 0$, and let $\varphi$ be a $d$-tuple of series in $X_1,\dots,X_d$ with zero constant terms, linear part the identity matrix, such that for every $N$ and $i$ all but finitely many coefficients of $\varphi_i$ lie in $(p^N)$, and such that $\varphi_i(F_p(X,Y)) = \varphi_i(X)+\varphi_i(Y)$ for all $i$. Fix $i$ and naturals $N,E$. The assertion is that there is $M_0$ with the following property for every $M \ge M_0$. Let $c : (\mathrm{Fin}\,d \to_0 \mathbb N) \to \mathcal O$ be any family such that for $\deg m \le M$ one has $c_m = p^{M-\deg m}\,\mathrm{coeff}_m(\varphi_i)$, while for $\deg m > M$ either $c_m\, p^{\deg m - M} = \mathrm{coeff}_m(\varphi_i)$, or $c_m = 0$ and $p^{\deg m - M} \nmid \mathrm{coeff}_m(\varphi_i)$. Let $\ell$ be a $p$-typical Witt vector over $\mathcal O[[X_1,\dots,X_d]]$ whose ghost components in degrees $n<M$ are given by $\mathrm{coeff}_{m'}(w_n(\ell)) = c_{p^{M-1-n}m'}$. Then for every $j$ with $M-N \le j < M$, the $j$-th Witt coefficient of $$W(\varphi \mapsto \varphi\circ F)(\ell) - W(X \mapsto X)(\ell) - W(X \mapsto Y)(\ell),$$ where the three maps are the Witt functor applied to substitution of $F$, of the first block of variables and of the second block of variables respectively, lies in the ideal $(p) + (X_1,\dots,X_d,Y_1,\dots,Y_d)^E$ of $\mathcal O[[X_1,\dots,X_d,Y_1,\dots,Y_d]]$.
--
--   This is a finite, truncated avatar of the statement that the covector attached to the logarithm of a formal group is a homomorphism into covectors: a Witt vector whose first $M$ ghost components are the rescaled logarithm coefficients fails to be additive along the group law only in its first components, and only modulo $p$ and modulo a high power of the augmentation ideal. It is used in the construction of the Witt-vector (Fontaine) description of $p$-divisible groups entering the deformation-theoretic part of the argument, being cited by [`Deformation.truncate_map_mem_wittHom_of_forall_coeff_ghostComponent_eq_logCovector`](thm.html#Deformation.truncate_map_mem_wittHom_of_forall_coeff_ghostComponent_eq_logCovector).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_coeff_map_subst_sub_map_sub_map_mem_of_forall_coeff_ghostComponent_eq_logCovector.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPowerSeries

universe u

theorem MvFormalGroup.coeff_map_subst_sub_map_sub_map_mem_of_forall_coeff_ghostComponent_eq_logCovector
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (i : Fin d) (N E : ℕ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ (c : (Fin d →₀ ℕ) → 𝓞),
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ M → c m = (p : 𝓞) ^ (M - m.degree) * (φ i).coeff m) ∧
        (M < m.degree → c m * (p : 𝓞) ^ (m.degree - M) = (φ i).coeff m ∨
          (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ (φ i).coeff m))) →
      ∀ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞),
        (∀ n : ℕ, n < M → ∀ m' : Fin d →₀ ℕ,
          (WittVector.ghostComponent n ℓ).coeff m' = c (p ^ (M - 1 - n) • m')) →
        ∀ j : ℕ, M - N ≤ j → j < M →
          (WittVector.map (MvPowerSeries.substAlgHom
                (MvPowerSeries.hasSubst_of_constantCoeff_zero F.constantCoeff_eq_zero)).toRingHom ℓ -
            WittVector.map (MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
                (fun j : Fin d => MvPowerSeries.constantCoeff_X (Sum.inl j) (R := 𝓞)))).toRingHom ℓ -
            WittVector.map (MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
                (fun j : Fin d => MvPowerSeries.constantCoeff_X (Sum.inr j) (R := 𝓞)))).toRingHom ℓ).coeff j ∈
            Ideal.span {(p : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)} ⊔
              (Ideal.span (Set.range (X : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞))) ^ E := by sorry
