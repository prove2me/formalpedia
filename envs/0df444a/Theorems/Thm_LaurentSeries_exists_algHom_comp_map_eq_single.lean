-- Prove2me | Theorems.Thm_LaurentSeries_exists_algHom_comp_map_eq_single
-- name    : LaurentSeries.exists_algHom_comp_map_eq_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/70dd59d7-5fd8-5e59-812a-b1c053ef17ff
-- title:
--   Order-preserving renormalisation of an embedding into K((X))
-- statement:
--   Let $K$ be a field that is algebraically closed and of characteristic zero, let $F$ be a field equipped with a $K$-algebra structure, and let $\varphi : F \to K((X))$ be a $K$-algebra homomorphism into the field of formal Laurent series over $K$ (Hahn series over $K$ with value group $\mathbb{Z}$). Let $f \in F$ be such that the order of $\varphi f$ is strictly positive; here `order` is the Hahn-series order, namely the least element of the support for a nonzero series and $0$ for the zero series, so the hypothesis in particular forces $\varphi f \neq 0$. The assertion is that there exists a further $K$-algebra homomorphism $\varphi' : F \to K((X))$ with two properties: for every $x \in F$ the order of $\varphi' x$ equals the order of $\varphi x$, and $\varphi' f$ is exactly the monomial `single (φ f).order 1`, that is, the Laurent series whose only nonzero coefficient is $1$, in degree equal to the order of $\varphi f$.
--
--   This is the Newton–Puiseux normalisation of a Laurent series of positive order over an algebraically closed field of characteristic zero, packaged as the statement that an embedding of a field into $K((X))$ may be replaced by an order-equivalent one sending a prescribed element of positive order to an exact power of the variable. It is used in the count [`ModularCurve.natCard_normalized_algHom_jBar_eq_toNat_ord`](thm.html#ModularCurve.natCard_normalized_algHom_jBar_eq_toNat_ord), where an embedding of a function field may be assumed to send the chosen parameter to a power of the uniformiser while all orders, and hence the place determined by the embedding, are unchanged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentSeries_exists_algHom_comp_map_eq_single.lean

import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries

theorem LaurentSeries.exists_algHom_comp_map_eq_single {K F : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (φ : F →ₐ[K] LaurentSeries K) (f : F) (hf : 0 < (φ f).order) :
    ∃ φ' : F →ₐ[K] LaurentSeries K,
      (∀ x : F, (φ' x).order = (φ x).order) ∧ φ' f = single (φ f).order 1 := by sorry
