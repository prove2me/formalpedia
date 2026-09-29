-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units
-- name    : NumberField.mixedEmbedding.contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/aa055564-58c1-541c-9224-2f69853f20f0
-- title:
--   Smoothness and support under inversion and the twist (a,b)↦(a,ba⁻¹)
-- statement:
--   Let $K$ be a number field and let $V$ denote its mixed space `mixedSpace K` (the product of one copy of $\mathbb{R}$ or $\mathbb{C}$ for each infinite place), a commutative ring with its natural real-normed structure; `Ring.inverse` is the ring inverse on $V$, extended by $0$ on non-units. The theorem is the conjunction of two independent assertions. First: for every $F : V \to \mathbb{C}$ that is $C^\infty$ over $\mathbb{R}$, and every compact set $C_0 \subseteq V$ all of whose points are units and such that $F\,y \neq 0$ forces $y \in C_0$, the function $y \mapsto F(\mathrm{inv}\,y)$ is $C^\infty$ over $\mathbb{R}$, the image $\mathrm{inv}(C_0)$ is compact and consists of units, and $F(\mathrm{inv}\,y) \neq 0$ forces $y \in \mathrm{inv}(C_0)$. Secondly: let $g : V \to \mathbb{C}$ be $C^\infty$ over $\mathbb{R}$ on the set $\{y : V \mid \mathrm{IsUnit}\,y\}$, let $B : (\mathrm{Fin}\,2 \to V) \to \mathbb{C}$ be $C^\infty$ over $\mathbb{R}$ with compact support, and let $C_p$ be a compact set of pairs of units of the infinite adele ring $\mathbb{A}_{K,\infty}$ such that every $p$ in the topological support of $B$ equals the pair $![\,\varphi(q_1), \varphi(q_2)\,]$ for some $(q_1,q_2) \in C_p$, where $\varphi$ is the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace K` applied to the underlying adeles. Then $p \mapsto g(p_0)\,B\,![\,p_0,\ p_1\cdot \mathrm{inv}(p_0)\,]$ is $C^\infty$ over $\mathbb{R}$, has compact support, and every point of its topological support is of the form $![\,\varphi(q_1), \varphi(q_2 q_1)\,]$ for some $(q_1,q_2) \in C_p$.
--
--   This is the elementary calculus underlying the change of variables $(a,b) \mapsto (a, b a^{-1})$ on the unit group of the mixed space, packaged so that smoothness, compactness of support, and the location of the support in terms of a compact set of pairs of infinite ideles are all transported at once. It is used in the archimedean window computations for the idele-class group, namely by [`NumberField.Idele.exists_contDiff_integral_mul_discArchWindow_prod_eq_add_sum_norm_sub_inv_mul_add_sum_of_isCompact`](thm.html#NumberField.Idele.exists_contDiff_integral_mul_discArchWindow_prod_eq_add_sum_norm_sub_inv_mul_add_sum_of_isCompact) and by [`NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le`](thm.html#NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical in

theorem NumberField.mixedEmbedding.contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units
    (K : Type) [Field K] [NumberField K] :
    (∀ (F : mixedSpace K → ℂ), ContDiff ℝ (⊤ : ℕ∞) F →
      ∀ (C₀ : Set (mixedSpace K)), IsCompact C₀ → (∀ y ∈ C₀, IsUnit y) → (∀ y, F y ≠ 0 → y ∈ C₀) →
        ContDiff ℝ (⊤ : ℕ∞) (fun y : mixedSpace K => F (Ring.inverse y)) ∧
        IsCompact (Ring.inverse '' C₀) ∧ (∀ y ∈ Ring.inverse '' C₀, IsUnit y) ∧
        ∀ y : mixedSpace K, F (Ring.inverse y) ≠ 0 → y ∈ Ring.inverse '' C₀) ∧
    (∀ (g : mixedSpace K → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) g {y : mixedSpace K | IsUnit y} →
      ∀ (B : (Fin 2 → mixedSpace K) → ℂ), ContDiff ℝ (⊤ : ℕ∞) B → HasCompactSupport B →
      ∀ (Cp : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)), IsCompact Cp →
        (∀ p ∈ tsupport B, ∃ q ∈ Cp,
          p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) →
        ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 2 → mixedSpace K => g (p 0) * B ![p 0, p 1 * Ring.inverse (p 0)]) ∧
        HasCompactSupport (fun p : Fin 2 → mixedSpace K => g (p 0) * B ![p 0, p 1 * Ring.inverse (p 0)]) ∧
        ∀ p ∈ tsupport (fun p : Fin 2 → mixedSpace K => g (p 0) * B ![p 0, p 1 * Ring.inverse (p 0)]),
          ∃ q ∈ (fun q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => (q.1, q.2 * q.1)) '' Cp,
            p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                  InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) := by sorry
