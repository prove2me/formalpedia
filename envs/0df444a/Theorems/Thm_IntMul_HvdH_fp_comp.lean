-- Prove2me | Theorems.Thm_IntMul_HvdH_fp_comp
-- name    : IntMul.HvdH.fp_comp
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T00:49:46.970514+00:00
-- url     : https://prove2.me/theorems/55104711-164b-4c32-a8b5-169d87d7d9f0
-- title:
--   Composition of fixed-point approximations (Corollary 2.8)
-- statement:
--   Let $\tilde A$ approximate $A$ with error $\varepsilon_1$ and $\tilde B$ approximate $B$ with error $\varepsilon_2$ at precision $p$, in the sense of `FPApprox` (`IntMul_HvdH_FPApprox`). Suppose $B$ is $1$-Lipschitz for the sup norm. Then $\tilde B\circ\tilde A$ approximates $B\circ A$ with error
--   $$\varepsilon(\tilde B\tilde A)\le\varepsilon_1+\varepsilon_2.$$
--   This is Corollary 2.8 of Harvey–van der Hoeven, stated for fixed-point arrays of Gaussian integers.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Corollary 2.8

import Definitions.Def_IntMul_HvdH_FPApprox

namespace IntMul.HvdH
theorem fp_comp {ι κ μ : Type*} (p : ℕ) {Aa : (ι → ℤ × ℤ) → (κ → ℤ × ℤ)} {A : (ι → ℂ) → (κ → ℂ)}
    {Ba : (κ → ℤ × ℤ) → (μ → ℤ × ℤ)} {B : (κ → ℂ) → (μ → ℂ)} {ε₁ ε₂ : ℝ}
    (hA : FPApprox p Aa A ε₁) (hB : FPApprox p Ba B ε₂) (hBl : SupLip B) :
    FPApprox p (Ba ∘ Aa) (B ∘ A) (ε₁ + ε₂) := by sorry
end IntMul.HvdH
