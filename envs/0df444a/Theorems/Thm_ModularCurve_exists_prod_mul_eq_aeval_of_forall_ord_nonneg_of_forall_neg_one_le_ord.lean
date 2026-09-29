-- Prove2me | Theorems.Thm_ModularCurve_exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord
-- name    : ModularCurve.exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/bfb40669-db66-58ee-afc6-e50225d4a1c4
-- title:
--   Clearing simple poles on the j-line gives a polynomial
-- statement:
--   Let $k$ be an algebraically closed field and let $\tilde\jmath \in k(\!(q)\!)$ denote the Laurent series `jqModC k`, namely $q^{-1}$ times the integral power series $E_4^3\,\eta^{-24}$ mapped into $k$; write $F =$ `modularFunctionFieldC k 1` for the intermediate field of $k(\!(q)\!)$ generated over $k$ by $\tilde\jmath$ (at level $1$). For a place $v$ of $F$ over $k$ in the project's sense (a proper valuation subring containing $k$ whose ideals are principal), $v.\mathrm{ord}$ is the associated normalised integer valuation. The points of $k$ index places of $F$ through the isomorphism $k(X) \cong F$ carrying $X$ to $\tilde\jmath$: `charLGeomPlaceOfPoint k b` is the transport of the place of $k(X)$ at $X - b$, and `charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)` the transport of the place at infinity. Given a finite set $S_0 \subseteq k$, a natural number $n$, and $\varphi \in F$ such that $\mathrm{ord}_b \varphi \ge 0$ for every $b \notin S_0$, $\mathrm{ord}_a \varphi \ge -1$ for every $a \in S_0$, and $\mathrm{ord}_\infty \varphi \ge -n$, the assertion is that there exists $Q \in k[X]$ with $\deg Q \le n + \#S_0$ whenever $Q \ne 0$, and with $\bigl(\prod_{a \in S_0} (\tilde\jmath - a)\bigr)\cdot \varphi = Q(\tilde\jmath)$ in $F$.
--
--   This is the Riemann–Roch computation for the $j$-line in the form in which it is used downstream: a rational function of $\tilde\jmath$ regular away from $S_0 \cup \{\infty\}$, with at most simple poles on $S_0$ and a pole of order at most $n$ at infinity, becomes a polynomial in $\tilde\jmath$ of controlled degree after multiplication by $\prod_{a\in S_0}(\tilde\jmath - a)$. It is the shape in which families of functions on the $j$-line with prescribed simple poles (e.g. at supersingular values) are recognised as polynomial, and is cited by the multiplicative-covering constructions on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord.lean

import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] [DecidableEq (RatFunc k)]
    (S₀ : Finset k) (n : ℕ) (φ : ↥(modularFunctionFieldC k 1))
    (hreg : ∀ b : k, b ∉ S₀ → 0 ≤ (charLGeomPlaceOfPoint k b).ord φ)
    (hS₀ : ∀ a ∈ S₀, -1 ≤ (charLGeomPlaceOfPoint k a).ord φ)
    (hinf : -(n : ℤ) ≤ (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord φ) :
    ∃ Q : Polynomial k, (Q ≠ 0 → Q.natDegree ≤ n + S₀.card) ∧
      (∏ a ∈ S₀, ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a)) * φ
        = Polynomial.aeval (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) Q := by sorry
