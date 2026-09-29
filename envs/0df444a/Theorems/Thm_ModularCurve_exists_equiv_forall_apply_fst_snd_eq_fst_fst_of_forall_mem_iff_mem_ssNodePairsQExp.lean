-- Prove2me | Theorems.Thm_ModularCurve_exists_equiv_forall_apply_fst_snd_eq_fst_fst_of_forall_mem_iff_mem_ssNodePairsQExp
-- name    : ModularCurve.exists_equiv_forall_apply_fst_snd_eq_fst_fst_of_forall_mem_iff_mem_ssNodePairsQExp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/7d29b09b-841f-5c18-807f-4bd38435a61c
-- title:
--   Frobenius shift permutes supersingular node pairs
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$ with $p$ prime, and let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$. Write $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the quotients $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ attached to integral $q$-expansions of modular forms of equal weight for $\Gamma$, and let places of $F$ over $K$ be understood in the project's sense: valuation subrings of $F$ containing $\mathrm{algebraMap}\,K\,F$, distinct from $F$ itself, and principal ideal rings. Let $T$ be a finite set of ordered pairs of such places, and assume that a pair $s$ lies in $T$ exactly when it lies in [`ModularCurve.ssNodePairsQExp K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L307), i.e. when $s_2$ satisfies the predicate `IsSSPlaceQExp` for $K,\Gamma,p$ and $s_1 =$ `qExpFrobeniusPlaceModL K Γ p` $s_2$, the restriction of $s_2$ along the Frobenius map `qExpFrobeniusModL K Γ p`. The conclusion is that there exists a bijection $\sigma$ of the coercion of $T$ to a type with itself such that for every $n \in T$ the second coordinate of $\sigma(n)$ equals the first coordinate of $n$.
--
--   The set in question is the set of supersingular node pairs in the $q$-expansion model, and the permutation produced is the Frobenius shift $(\mathrm{Frob}\,y, y) \mapsto (\mathrm{Frob}^2 y, \mathrm{Frob}\,y)$ on it. It supplies the node permutation used in the bookkeeping for the special fibre of the Néron model of the Jacobian at $p$, and is cited in the statements about prolongation data, Tate modules of $J_H$ and inertia at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_equiv_forall_apply_fst_snd_eq_fst_fst_of_forall_mem_iff_mem_ssNodePairsQExp.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_equiv_forall_apply_fst_snd_eq_fst_fst_of_forall_mem_iff_mem_ssNodePairsQExp
    (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (T : Finset (AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K Γ) ×
      AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K Γ)))
    (hT : ∀ s, s ∈ T ↔ s ∈ ModularCurve.ssNodePairsQExp K Γ p) :
    ∃ σ : ↥T ≃ ↥T, ∀ n : ↥T, (σ n).1.2 = n.1.1 := by sorry
