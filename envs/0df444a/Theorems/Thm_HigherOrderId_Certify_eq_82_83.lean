-- Prove2me | Theorems.Thm_HigherOrderId_Certify_eq_82_83
-- name    : HigherOrderId.Certify.eq_82_83
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:17:55.793375+00:00
-- url     : https://prove2.me/theorems/e940a859-111d-42bc-b737-aef46122f5e8
-- title:
--   §B.5, Eqs. (82)–(83) — ‖D_U‖_{S1} ≤ m, hence Σ a_j^{-2} ≥ t³/m² ≳ m⁴ and Σ a_j^{-4} ≥ t⁵/m⁴ ≳ m⁶ for every orthonormal U
-- statement:
--   Let $d\ge10$ and let $U\in\mathbb R^{d\times m}$ have orthonormal columns, with rows $u_a^\top$. The nuclear norm of $D_U$ (the sum of its $t=m(m+1)/2$ singular values) satisfies
--   $$\|D_U\|_{S_1}\le\sum_{a=1}^d\|u_au_a^\top\|_F=m.\tag{82}$$
--   If moreover $m\ge1$ and $D_U$ has full column rank with singular values $a_1,\dots,a_t>0$, then for $s\in\{2,4\}$
--   $$\frac1t\sum_ja_j^{-s}\ge\Big(\frac1t\sum_ja_j\Big)^{-s}\ge\Big(\frac mt\Big)^{-s},$$
--   and hence, with a universal constant $c>0$,
--   $$\sum_{j=1}^ta_j^{-2}\ge\frac{t^3}{m^2}\ge c\,m^4,\qquad\sum_{j=1}^ta_j^{-4}\ge\frac{t^5}{m^4}\ge c\,m^6.\tag{83}$$
--
--   These are the universal inverse-spectrum lower bounds that the weighted frame of Lemma B.4 attains.
--
--   Differences from the source:
--   - encoding: ‖D_U‖_{S1} → Σ_j a_j, the sum of the singular values; reason: definition of the Schatten-1 (nuclear) norm
--   - encoding: ≳ m⁴, ≳ m⁶ → ∃ universal c > 0 (before d, m, U) with t³/m² ≥ c m⁴ and t⁵/m⁴ ≥ c m⁶; reason: explicit form of ≳
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 26, §B.5, Eqs. (82)–(83) (PDF p. 27)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Completion

open Matrix

namespace HigherOrderId.Certify

/-- §B.5, Eqs. (82)–(83) (universal inverse-spectrum lower bound). For every `d × m` matrix `U`
with orthonormal columns (rows `u_aᵀ`), the nuclear norm of `D_U`, the sum of its `t` singular
values, is at most `Σ_a ‖u_a u_aᵀ‖_F = m` (82). If `m ≥ 1` and `D_U` has full column rank then,
for `s ∈ {2, 4}`, `(1/t) Σ_j a_j^{-s} ≥ ((1/t) Σ_j a_j)^{-s} ≥ (m/t)^{-s}`, and
`Σ_j a_j^{-2} ≥ t³/m² ≳ m⁴`, `Σ_j a_j^{-4} ≥ t⁵/m⁴ ≳ m⁶` (83), with a universal constant. -/
theorem eq_82_83 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d m : ℕ) (U : Matrix (Fin d) (Fin m) ℝ), 10 ≤ d → Uᵀ * U = 1 →
        (∑ j, singVals U j ≤ ∑ a, frobNorm (vecMulVec (U a) (U a))) ∧
        (∑ a, frobNorm (vecMulVec (U a) (U a)) = (m : ℝ)) ∧
        (1 ≤ m → FullColRank U →
          (∀ s ∈ ({2, 4} : Finset ℕ),
            ((1 / (Fintype.card (SymIdx m) : ℝ)) * ∑ j, singVals U j)⁻¹ ^ s ≤
                (1 / (Fintype.card (SymIdx m) : ℝ)) * ∑ j, (singVals U j)⁻¹ ^ s ∧
            ((m : ℝ) / (Fintype.card (SymIdx m) : ℝ))⁻¹ ^ s ≤
                ((1 / (Fintype.card (SymIdx m) : ℝ)) * ∑ j, singVals U j)⁻¹ ^ s) ∧
          (Fintype.card (SymIdx m) : ℝ) ^ 3 / (m : ℝ) ^ 2 ≤ ∑ j, (singVals U j)⁻¹ ^ 2 ∧
          c * (m : ℝ) ^ 4 ≤ (Fintype.card (SymIdx m) : ℝ) ^ 3 / (m : ℝ) ^ 2 ∧
          (Fintype.card (SymIdx m) : ℝ) ^ 5 / (m : ℝ) ^ 4 ≤ ∑ j, (singVals U j)⁻¹ ^ 4 ∧
          c * (m : ℝ) ^ 6 ≤ (Fintype.card (SymIdx m) : ℝ) ^ 5 / (m : ℝ) ^ 4) := by sorry

end HigherOrderId.Certify
