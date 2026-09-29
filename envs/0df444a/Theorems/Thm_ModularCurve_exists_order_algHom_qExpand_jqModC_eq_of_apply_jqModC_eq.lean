-- Prove2me | Theorems.Thm_ModularCurve_exists_order_algHom_qExpand_jqModC_eq_of_apply_jqModC_eq
-- name    : ModularCurve.exists_order_algHom_qExpand_jqModC_eq_of_apply_jqModC_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/9b0825e6-d580-50d0-a14f-5a4bc21ddfd3
-- title:
--   Order of ι(jmath̄(qᵈ)) equals -(N/d)a'² for some a' ∣ d
-- statement:
--   Let $K$ be an algebraically closed field and $N \ge 1$ a natural number whose image in $K$ is non-zero. Write $\bar\jmath =$ `jqModC K` for the Laurent series $q^{-1}$ times the power series $E_4^3\cdot\eta^{-24}$ with coefficients pushed into $K$, and for $e \ge 1$ write `qExpand K e` for the ring endomorphism of $K((q))$ given by multiplying all exponents by $e$, i.e. the substitution $q \mapsto q^e$. Let $F =$ `modularFunctionFieldFullC K N` be the intermediate field of $K((q))$ generated over $K$ by the set of all $\bar\jmath(q^e)$ with $e \ge 1$ and $e \mid N$, and let $\iota \colon F \to K((q))$ be a $K$-algebra homomorphism such that $\iota(\bar\jmath) = \bar\jmath(q^N)$. Then for every $d \ge 1$ dividing $N$ there exists a natural number $a'$ with $a' \mid d$ and $a' > 0$ such that the order of $\iota(\bar\jmath(q^d))$, that is the least exponent occurring in this Laurent series, equals $-\,(N/d)\,a'^2$ as an integer.
--
--   The possible $q$-orders of the generators $\bar\jmath(q^d)$ under an embedding of the level-$N$ modular function field into $K((q))$ normalised by $\bar\jmath \mapsto \bar\jmath(q^N)$; classically these are the cusp data of $\Gamma_0(N)$, coming from the matrices $\begin{pmatrix} a' & b' \\ 0 & d/a'\end{pmatrix}$. It is used to show that such an order is non-zero in $K$, in [`ModularCurve.cast_natAbs_ord_qExpand_jqModC_ne_zero_of_ord_neg`](thm.html#ModularCurve.cast_natAbs_ord_qExpand_jqModC_ne_zero_of_ord_neg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_order_algHom_qExpand_jqModC_eq_of_apply_jqModC_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_order_algHom_qExpand_jqModC_eq_of_apply_jqModC_eq
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (ι : ↥(modularFunctionFieldFullC K N) →ₐ[K] LaurentSeries K)
    (hι : ι ⟨jqModC K, jqModC_mem_full K N⟩ = qExpand K N (jqModC K))
    (d : ℕ) [NeZero d] (hd : d ∣ N) :
    ∃ a' : ℕ, a' ∣ d ∧ 0 < a' ∧
      (ι ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩).order = -((N / d * (a' * a') : ℕ) : ℤ) := by sorry
