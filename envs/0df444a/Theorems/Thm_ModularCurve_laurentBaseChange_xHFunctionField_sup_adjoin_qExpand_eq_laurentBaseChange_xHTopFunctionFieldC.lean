-- Prove2me | Theorems.Thm_ModularCurve_laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_eq_laurentBaseChange_xHTopFunctionFieldC
-- name    : ModularCurve.laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_eq_laurentBaseChange_xHTopFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/19caea0b-1dde-596f-a7ea-e8590b55e0e3
-- title:
--   Degeneracy compositum for Γ_{H'}(N)∩Γ₀(Nq) over a base field L
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $N$ and $q$ be positive natural numbers, and let $H'$ be a subgroup of $(\mathbb{Z}/N\mathbb{Z})^{\times}$. Write $\Gamma_{H'}$ for the subgroup [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133) of $SL_2(\mathbb{Z})$, the image in $SL_2(\mathbb{Z})$ of the preimage of $H'$ under `gamma0Units N` on $\Gamma_0(N)$. For a subgroup $\Gamma \le SL_2(\mathbb{Z})$, `qExpFunctionFieldC ℚ Γ` is the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the set `intFormRatiosC ℚ Γ`, and for an intermediate field $F_0$ of $\mathbb{Q}((q))$, `laurentBaseChange L F₀` is the intermediate field of $L((q))$ generated over $L$ by the coefficientwise image of $F_0$ under the map induced by $\mathbb{Q} \to L$. Finally `qExpand L q` is the ring endomorphism of $L((q))$ multiplying all exponents by $q$, i.e. the substitution $f(q) \mapsto f(q^{q})$. The assertion is that, inside $L((q))$, the join of $E :=$ `laurentBaseChange L (xHFunctionField N H')` with the intermediate field generated over $L$ by the image of (the underlying set of) $E$ under `qExpand L q` equals `laurentBaseChange L` applied to `qExpFunctionFieldC ℚ (Γ_{H'} ⊓ Gamma0 (N * q))`.
--
--   This is the statement that the $q$-expansion function field of the roof $\Gamma_{H'}(N) \cap \Gamma_0(Nq)$ of the Hecke correspondence of index $q$ on $X_{H'}(N)$, after base change to $L$, is the compositum of the images of the two degeneracy embeddings, the identity and the substitution $q \mapsto q^{q}$ (classically $\tau \mapsto q\tau$). It is used in the corresponding statement for the field denoted `xHFunctionFieldBar`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_eq_laurentBaseChange_xHTopFunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_eq_laurentBaseChange_xHTopFunctionFieldC
    (L : Type*) [Field L] [Algebra ℚ L] (N q : ℕ) [NeZero N] [NeZero q] (H' : Subgroup (ZMod N)ˣ) :
    laurentBaseChange L (xHFunctionField N H') ⊔
        IntermediateField.adjoin L (⇑(qExpand L q) '' (laurentBaseChange L (xHFunctionField N H') : Set (LaurentSeries L))) =
      laurentBaseChange L (xHTopFunctionFieldC ℚ N H' (N * q)) := by sorry
