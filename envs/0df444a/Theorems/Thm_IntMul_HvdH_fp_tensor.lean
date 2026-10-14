-- Prove2me | Theorems.Thm_IntMul_HvdH_fp_tensor
-- name    : IntMul.HvdH.fp_tensor
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T00:51:33.918136+00:00
-- url     : https://prove2.me/theorems/b9c60edd-1008-415b-9dae-fad6edc7e11a
-- title:
--   Fixed-point tensor products of approximations (Lemma 2.11)
-- statement:
--   For $i<d$ let $\tilde A_i$ approximate the one-dimensional map $A_i$ with error $\varepsilon_i$ at precision $p$ (see `IntMul_HvdH_FPApprox`), and let each $A_i$ be $1$-Lipschitz for the sup norm. Then applying the $\tilde A_i$ slice by slice (`tensorMapZ`) approximates the tensor product $\bigotimes_iA_i$ (`tensorMap`) with error
--   $$\varepsilon\Bigl(\bigotimes_i\tilde A_i\Bigr)\le\sum_i\varepsilon_i.$$
--   This is the error part of Lemma 2.11 of Harvey–van der Hoeven.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 2.11

import Definitions.Def_IntMul_HvdH_FPApprox

namespace IntMul.HvdH
theorem fp_tensor {d : ℕ} (p : ℕ) (Aa : Fin d → (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ))
    (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (ε : Fin d → ℝ)
    (hA : ∀ i, FPApprox p (Aa i) (A i) (ε i)) (hL : ∀ i, SupLip (A i)) :
    FPApprox p (tensorMapZ Aa) (tensorMap A) (∑ i, ε i) := by sorry
end IntMul.HvdH
