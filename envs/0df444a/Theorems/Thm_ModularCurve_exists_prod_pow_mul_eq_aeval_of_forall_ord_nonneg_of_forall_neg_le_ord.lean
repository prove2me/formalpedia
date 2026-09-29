-- Prove2me | Theorems.Thm_ModularCurve_exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord
-- name    : ModularCurve.exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/8e249da6-c4f3-598f-a73b-c8b4cae1b065
-- title:
--   Clearing prescribed poles on the j-line by polynomials
-- statement:
--   Let $k$ be an algebraically closed field (with decidability assumptions on $k$ and on $\mathrm{RatFunc}\,k$ carried along), and let $k(\tilde\jmath) =$ `modularFunctionFieldC k 1` be the subfield of the Laurent series field $k(\!(q)\!)$ generated over $k$ by the $q$-expansion `jqModC k` $= q^{-1}\cdot (E_4^3\,\eta^{-24})$ and by its level-one rescaling. Let $S_0 \subseteq k$ be a finite set, $m\colon k \to \mathbb{N}$ any function, $n \in \mathbb{N}$, and $\varphi \in k(\tilde\jmath)$. Places here are valuation subrings of $k(\tilde\jmath)$ containing $k$, proper and with principal ideals, and $\mathrm{ord}$ is the associated normalised additive valuation. Assume: $\mathrm{ord}_{v}\varphi \ge 0$ at the place attached to each point $b \notin S_0$ (the transport of the $X - b$-adic place of $k(X)$ along the isomorphism $k(X) \cong k(\tilde\jmath)$ sending $X$ to $\tilde\jmath$); $\mathrm{ord}\,\varphi \ge -m(a)$ at the place attached to each $a \in S_0$; and $\mathrm{ord}\,\varphi \ge -n$ at the transport of the place at infinity of $k(X)$. Then there is $Q \in k[X]$ such that $\bigl(\prod_{a \in S_0}(\tilde\jmath - a)^{m(a)}\bigr)\varphi = Q(\tilde\jmath)$, and $\deg Q \le n + \sum_{a\in S_0} m(a)$ unless $Q = 0$.
--
--   This is Riemann–Roch on the $j$-line in its elementary form: a rational function of $\tilde\jmath$ with poles bounded by the divisor $n\cdot\infty + \sum_{a\in S_0} m(a)\,(a)$ becomes a polynomial of controlled degree after multiplication by the obvious denominator. It is used in the construction of the component charts of $X_0(p)$, where nodes of higher width force pole multiplicities greater than one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord.lean

import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] [DecidableEq (RatFunc k)]
    (S₀ : Finset k) (m : k → ℕ) (n : ℕ) (φ : ↥(modularFunctionFieldC k 1))
    (hreg : ∀ b : k, b ∉ S₀ → 0 ≤ (charLGeomPlaceOfPoint k b).ord φ)
    (hS₀ : ∀ a ∈ S₀, -(m a : ℤ) ≤ (charLGeomPlaceOfPoint k a).ord φ)
    (hinf : -(n : ℤ) ≤ (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord φ) :
    ∃ Q : Polynomial k, (Q ≠ 0 → Q.natDegree ≤ n + ∑ a ∈ S₀, m a) ∧
      (∏ a ∈ S₀, ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a) ^ m a) * φ
        = Polynomial.aeval (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) Q := by sorry
