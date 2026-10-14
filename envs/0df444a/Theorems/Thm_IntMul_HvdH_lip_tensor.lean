-- Prove2me | Theorems.Thm_IntMul_HvdH_lip_tensor
-- name    : IntMul.HvdH.lip_tensor
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T00:50:36.541989+00:00
-- url     : https://prove2.me/theorems/e2622578-7037-4190-82de-9a7819c6449d
-- title:
--   Tensor products of 1-Lipschitz maps are 1-Lipschitz
-- statement:
--   If each one-dimensional map $A_i$ ($i<d$) is $1$-Lipschitz for the sup norm (`SupLip`, see `IntMul_HvdH_FPApprox`), then so is the slice-by-slice tensor product $\bigotimes_iA_i$ (`tensorMap`). For linear maps this is $\|\bigotimes_iA_i\|\le1$ when every $\|A_i\|\le1$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, §2.7

import Definitions.Def_IntMul_HvdH_FPApprox

namespace IntMul.HvdH
theorem lip_tensor {d : ℕ} (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (hL : ∀ i, SupLip (A i)) :
    SupLip (tensorMap A) := by sorry
end IntMul.HvdH
