-- Prove2me | Theorems.Thm_LefebvreVariations_sum_product_exponent_four_thirds
-- name    : LefebvreVariations.sum_product_exponent_four_thirds
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:04:09.241637+00:00
-- url     : https://prove2.me/theorems/0e12c877-4d2e-4971-b8c5-0b37aac9e792
-- title:
--   Lefebvre's variations, No. 118 — on a theme by Paul Erdős and Endre Szemerédi: the sum-product exponent four thirds for integers
-- statement:
--   There is a constant $C>0$ such that for every finite nonempty set $A\subset\mathbb{Z}$,
--   $$
--   \max\bigl(|A+A|,\ |A\cdot A|\bigr)\ \ge\ C\,|A|^{4/3}.
--   $$
--   Here $A+A=\{a+b\}$ and $A\cdot A=\{ab\}$ over $a,b\in A$. The Erdős–Szemerédi conjecture asserts the same with exponent $2-\varepsilon$ for every $\varepsilon>0$; the exponent $4/3$ is an unconditional case. This follows from Solymosi's bound and its improvements by Konyagin and Shkredov to exponent $4/3+c$.
--
--   **Formalization Note** The statement is the platform's `erdos_szemeredi_sum_product` with the exponent `2 - eps` replaced by the real number `4 / 3` (that is, `eps = 2/3` in the parent's form). Sets are `Finset ℤ`, the sumset and product set are the images of `A ×ˢ A`, and the bound is a real inequality.
--
--   **Why this is a variation.** A variation on the platform's open `erdos_szemeredi_sum_product` (exponent 2 - eps): it fixes the exponent to the known partial result 4/3. The conjecture for every eps > 0 remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   J. Solymosi, Bounding multiplicative energy by the sumset, Adv. Math. 222 (2009) (exponent 4/3 up to a logarithmic factor; cited from memory, not verified). S. V. Konyagin and I. D. Shkredov, On sum sets of sets having small product set, Proc. Steklov Inst. Math. 290 (2015) 288-299 (bibliographic data verified by web search; the abstract-level claim max(|A+A|,|AA|) >> |A|^(4/3+c) for real sets, c>0 absolute, is as reported in the arXiv version 1503.05771). Parent: Erdos and Szemeredi, On sums and products of integers (1983), on the platform as `erdos_szemeredi_sum_product` (open).

import Mathlib

namespace LefebvreVariations

/-- Sum-product lower bound `max(|A+A|, |A·A|) ≥ C |A|^(4/3)` for finite sets of integers. Source: J. Solymosi, Bounding multiplicative energy by the sumset, Adv. Math. 222 (2009) 402-408 (exponent 4/3 up to a logarithm), and the removal of the logarithm with a power gain by Konyagin and Shkredov, On sum sets of sets having small product set, Proc. Steklov Inst. Math. 290 (2015) 288-299 (cited from memory). -/
theorem sum_product_exponent_four_thirds :
    ∃ C : ℝ, 0 < C ∧
    ∀ (A : Finset ℤ), A.Nonempty →
      C * (A.card : ℝ) ^ (4 / 3 : ℝ) ≤
      max ((A ×ˢ A).image (fun p => p.1 + p.2)).card
          ((A ×ˢ A).image (fun p => p.1 * p.2)).card := by
  sorry

end LefebvreVariations
