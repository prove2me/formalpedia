-- Prove2me | Theorems.Thm_KelnerLinSolve_test_eq_13
-- name    : KelnerLinSolve.test_eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:55:35.485838+00:00
-- url     : https://prove2.me/theorems/c531a09d-f4c9-477a-b1a1-0b88dbf2f3de
-- title:
--   §4.3, (13) — the acceptance test (8) as $n$ integer comparisons
-- statement:
--   Let $E, R, S\in\mathbb N$, and let $z_i = a_i/g_i$ with integers $a_i$ and $g_i>0$ ($1\le i\le n$). Put $y = Rz$ and $\varepsilon = 2^{-E}$. Then
--
--   $$
--   8n^2(\|y\|_\infty+1)\le\varepsilon S \iff 2^E\cdot8n^2\,(R|a_i|+g_i)\le S\,g_i\quad\text{for all } 1\le i\le n. \tag{13}
--   $$
--
--   The test therefore uses only the exact reconstructed fractions and integer arithmetic, never products with the floating-point data.
--
--   Differences from the source:
--   - generalization: R and S powers of two → any natural numbers R, S; reason: the equivalence holds for all of them and specializes
--   - encoding: 2^E 8n² → the product 2^E · 8 · n²; reason: the page's juxtaposition is a product
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), §4.3, p.14, Equation (13)

import Mathlib
import Definitions.Def_KelnerLinSolve_kappa2

namespace KelnerLinSolve

/-- **§4.3, the acceptance test as integer comparisons, Equation (13)**, Kelner, *Solving Linear
Systems in Õ(mn log(κ/ε)) Bit Operations*, STOC 2027 submission (sha256 d1af55cb…), p.14. "The test
uses only the exact reconstructed fractions, not products with the original floating-point data. If
`zᵢ = aᵢ/gᵢ` with `gᵢ > 0`, it is equivalent to the `n` integer comparisons
`2^E 8n²(R|aᵢ| + gᵢ) ≤ Sgᵢ (1 ≤ i ≤ n)`. (13)"

With `y = Rz` and `ε = 2^{−E}`, the test (8) `8n²(‖y‖_∞ + 1) ≤ εS` holds if and only if all `n`
comparisons (13) hold, for every representation `zᵢ = aᵢ/gᵢ` with integers `aᵢ` and `gᵢ > 0`.

**Formalization Note.** `2^E 8n²` is the product `2^E · 8 · n²`. `R` and `S` are any natural numbers
(on the page they are powers of two). -/
theorem test_eq_13 {n : ℕ} (E R S : ℕ) (a g : Fin n → ℤ) (hg : ∀ i, 0 < g i) :
    let y : Fin n → ℝ := fun i => (R : ℝ) * ((a i : ℝ) / (g i : ℝ))
    (8 * (n : ℝ) ^ 2 * (infNorm y + 1) ≤ (2 : ℝ) ^ (-(E : ℤ)) * S ↔
      ∀ i, (2 : ℤ) ^ E * 8 * (n : ℤ) ^ 2 * ((R : ℤ) * |a i| + g i) ≤ (S : ℤ) * g i) := by sorry

end KelnerLinSolve
