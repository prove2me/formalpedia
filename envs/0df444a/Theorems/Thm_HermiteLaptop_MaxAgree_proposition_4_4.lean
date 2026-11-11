-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_proposition_4_4
-- name    : HermiteLaptop.MaxAgree.proposition_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:17:11.969213+00:00
-- url     : https://prove2.me/theorems/27bf947e-ab8c-4965-b494-b0a436c75f05
-- title:
--   Proposition 4.4 — for the 0.364/0.636 mixture of 4- and 5-spokes, P̲_24(ρ) ≥ 0.7818ρ on [0, 1] with rational lower bounds on c_{k,m}
-- statement:
--   For the mixture of the 4-spokes and 5-spokes roundings with probabilities $0.364$ and $0.636$, there are rational lower bounds $\underline c_{k,m}\le c_{k,m}$ ($k\in\{4,5\}$, $0\le m\le24$) such that
--   $$\underline P_{24}(\rho)=0.364\sum_{m=0}^{24}\underline c_{4,m}\rho^m+0.636\sum_{m=0}^{24}\underline c_{5,m}\rho^m\ \ge\ 0.7818\,s^+_0(\rho)=0.7818\,\rho\qquad\text{for all }\rho\in[0,1].$$
--   In the paper the bounds are the exact rational data generated as described in its §3.5. With Lemma 4.2 this yields the positive-edge inequality for $\gamma=0.7818$, $a=0$.
--
--   **Formalization Note.** Stated as an existential over the unprinted rational data; on $[0,1]$, $\underline P_{k,24}$ uses only the lower bounds.
--
--   Differences from the source:
--   - reading: "with the exact rational lower bounds on c_{k,m} generated as described in Section 3.5" (data not printed) → ∃ rationals c̲_{k,m} ≤ c_{k,m} (k ∈ {4,5}, m ≤ 24) satisfying the inequality; reason: the data lives in the authors' repository; the existential is exactly what Lemma 4.2 consumes
--   - encoding: P̲_24(ρ) and 0.7818 s⁺_0(ρ) on [0, 1] → 0.364 Σ_{m≤24} c̲_{4,m}ρ^m + 0.636 Σ_{m≤24} c̲_{5,m}ρ^m and 0.7818 ρ; reason: the [0,1] branch of P̲_{k,24} and s⁺_0(ρ) = ρ
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 29 (PDF 32), Proposition 4.4

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Hermite

namespace HermiteLaptop.MaxAgree

/-- Proposition 4.4: there are rational lower bounds `c̲_{k,m} ≤ c_{k,m}` (`k ∈ {4, 5}`,
`m ≤ 24`) such that `P̲_24(ρ) = 0.364 Σ_{m≤24} c̲_{4,m} ρᵐ + 0.636 Σ_{m≤24} c̲_{5,m} ρᵐ ≥
0.7818 ρ = 0.7818 s⁺_0(ρ)` for all `ρ ∈ [0, 1]`. -/
theorem proposition_4_4 :
    ∃ cl : ℕ → ℕ → ℚ,
      (∀ k ∈ ({4, 5} : Finset ℕ), ∀ m ≤ 24, (cl k m : ℝ) ≤ coeffC k m) ∧
      ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
        (0.7818 : ℝ) * ρ ≤
          0.364 * ∑ m ∈ Finset.range 25, (cl 4 m : ℝ) * ρ ^ m +
          0.636 * ∑ m ∈ Finset.range 25, (cl 5 m : ℝ) * ρ ^ m := by sorry

end HermiteLaptop.MaxAgree
