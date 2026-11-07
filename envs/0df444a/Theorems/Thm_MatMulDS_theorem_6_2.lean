-- Prove2me | Theorems.Thm_MatMulDS_theorem_6_2
-- name    : MatMulDS.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:07:23.68256+00:00
-- url     : https://prove2.me/theorems/197fad97-e395-4f32-945a-cbd0be861d45
-- title:
--   Theorem 6.2 — the enlarged identities with central lengths 8, 184, 104416
-- statement:
--   Applying Lemma 6.1 to the tensor square of the five-term identity, and then twice more, each time to the tensor square of the identity just obtained, gives bijective identities for block tensors with $5^2,5^4,5^8$ products, which have strict weight functions. Each has the same outputs and lengths as the tensor square of the previous one, except that its central output has length $d'=d^2+2ab$, with $a=n_A-d$, $b=n_B-d$. The central lengths and scores are:
--   $$\begin{array}{ccc}\text{products}&\text{central length}&\text{score}\\5&2&0.1722706\\5^2&8&0.1894977\\5^4&184&0.1900226\\5^8&104416&0.1900231\end{array}$$
--
--   These are the identities the mission's data structures use.
--
--   Differences from the source:
--   - reading: "Applying Lemma 6.1 … gives" identities → existence of identities related by `IsEnlargement`; reason: the proof of Lemma 6.1 makes choices (a basis extension), so there is no canonical identity
--   - encoding: table (6.9) prints scores to seven places → the exact score from (6.7), and within $5\cdot10^{-8}$ of the printed value; reason: (6.9) is rounded; exact values $0.17227062, 0.18949769, 0.19002262, 0.19002306$
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 6.2 and table (6.9), p.43 (PDF p.45); (6.4), p.37 (PDF p.39); (6.7), p.42 (PDF p.44)

import Mathlib
import Definitions.Def_MatMulDS_fiveTensor
import Definitions.Def_MatMulDS_IsEnlargement

set_option autoImplicit false

namespace MatMulDS

/-- **Theorem 6.2 (The Enlarged Identities), p.43, with table (6.9)** (Alman, Nogler, Vassilevska Williams, STOC 2027
submission, held file sha256 6c5a1c16…). Applying Lemma 6.1 to the tensor square of the five-term identity, and then
twice more, each time to the tensor square of the identity just obtained, gives bijective identities for block tensors
with `5²`, `5⁴`, `5⁸` products, which have strict weight functions. Each has the same outputs, with the same lengths, as
the tensor square of the previous one, except that its central output has the length `d′ = d² + 2ab` of (6.4), with
`a = n_A − d` and `b = n_B − d`. The central lengths are `2, 8, 184, 104416`, and the scores are those of (6.9).

**Formalization Note** The proof of Lemma 6.1 makes choices, so there is no canonical identity: the theorem is an
existence statement over the identities related by `IsEnlargement`. Table (6.9) prints the scores rounded to seven
places: the statement gives the exact score (from (6.7)) and that it is within `5·10⁻⁸` of the printed value. The
numbers of products are the cardinalities of the index types `(Fin 5)²`, and so on. -/
theorem theorem_6_2 :
    (fiveTensor.mids 1).card = 2 ∧ IsBijective fiveTensor (Fin 5) ∧
    HasStrictWeight fiveTensor fiveData ∧
    score fiveTensor (Fin 5) = 2 * Real.log 2 / (5 * Real.log 5) ∧
    |score fiveTensor (Fin 5) - 0.1722706| ≤ 5e-8 ∧
    ∃ (n₁ n₂ n₃ : ℕ)
      (T₁ : BlockTensor (Fin 3 × Fin 3) ((Fin 2 × Fin 2) ⊕ Fin n₁) (Fin 2 × Fin 2) (Fin 2 × Fin 2))
      (D₁ : IdentityData (Fin 3 × Fin 3) ((Fin 2 × Fin 2) ⊕ Fin n₁) (Fin 2 × Fin 2) (Fin 5 × Fin 5))
      (T₂ : BlockTensor ((Fin 3 × Fin 3) × (Fin 3 × Fin 3))
        ((((Fin 2 × Fin 2) ⊕ Fin n₁) × ((Fin 2 × Fin 2) ⊕ Fin n₁)) ⊕ Fin n₂)
        ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)))
      (D₂ : IdentityData ((Fin 3 × Fin 3) × (Fin 3 × Fin 3))
        ((((Fin 2 × Fin 2) ⊕ Fin n₁) × ((Fin 2 × Fin 2) ⊕ Fin n₁)) ⊕ Fin n₂)
        ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 5 × Fin 5) × (Fin 5 × Fin 5)))
      (T₃ : BlockTensor (((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) × ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)))
        ((((((Fin 2 × Fin 2) ⊕ Fin n₁) × ((Fin 2 × Fin 2) ⊕ Fin n₁)) ⊕ Fin n₂) ×
          (((((Fin 2 × Fin 2) ⊕ Fin n₁) × ((Fin 2 × Fin 2) ⊕ Fin n₁))) ⊕ Fin n₂)) ⊕ Fin n₃)
        (((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) × ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)))
        (((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) × ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))))
      (D₃ : IdentityData (((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) × ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)))
        ((((((Fin 2 × Fin 2) ⊕ Fin n₁) × ((Fin 2 × Fin 2) ⊕ Fin n₁)) ⊕ Fin n₂) ×
          (((((Fin 2 × Fin 2) ⊕ Fin n₁) × ((Fin 2 × Fin 2) ⊕ Fin n₁))) ⊕ Fin n₂)) ⊕ Fin n₃)
        (((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) × ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)))
        (((Fin 5 × Fin 5) × (Fin 5 × Fin 5)) × ((Fin 5 × Fin 5) × (Fin 5 × Fin 5)))),
      IsEnlargement fiveTensor.square fiveData.square (1, 1)
        (BlockTensor.squareOut ((2 : Fin 3), (0 : Fin 2))) T₁ D₁ ∧
      IsEnlargement T₁.square D₁.square ((1, 1), (1, 1))
        (BlockTensor.squareOut (BlockTensor.squareOut ((2 : Fin 3), (0 : Fin 2)))) T₂ D₂ ∧
      IsEnlargement T₂.square D₂.square (((1, 1), (1, 1)), ((1, 1), (1, 1)))
        (BlockTensor.squareOut (BlockTensor.squareOut (BlockTensor.squareOut ((2 : Fin 3), (0 : Fin 2)))))
        T₃ D₃ ∧
      IsBijective T₁ (Fin 5 × Fin 5) ∧
      IsBijective T₂ ((Fin 5 × Fin 5) × (Fin 5 × Fin 5)) ∧
      IsBijective T₃ (((Fin 5 × Fin 5) × (Fin 5 × Fin 5)) × ((Fin 5 × Fin 5) × (Fin 5 × Fin 5))) ∧
      HasStrictWeight T₁ D₁ ∧ HasStrictWeight T₂ D₂ ∧ HasStrictWeight T₃ D₃ ∧
      -- the central lengths: `d′ = d² + 2ab`, and their values
      (T₁.mids (1, 1)).card = (fiveTensor.mids 1).card ^ 2 +
        2 * (fiveTensor.leftVars.card - (fiveTensor.mids 1).card) *
          (fiveTensor.rightVars.card - (fiveTensor.mids 1).card) ∧
      (T₂.mids ((1, 1), (1, 1))).card = (T₁.mids (1, 1)).card ^ 2 +
        2 * (T₁.leftVars.card - (T₁.mids (1, 1)).card) *
          (T₁.rightVars.card - (T₁.mids (1, 1)).card) ∧
      (T₃.mids (((1, 1), (1, 1)), ((1, 1), (1, 1)))).card = (T₂.mids ((1, 1), (1, 1))).card ^ 2 +
        2 * (T₂.leftVars.card - (T₂.mids ((1, 1), (1, 1))).card) *
          (T₂.rightVars.card - (T₂.mids ((1, 1), (1, 1))).card) ∧
      (T₁.mids (1, 1)).card = 8 ∧
      (T₂.mids ((1, 1), (1, 1))).card = 184 ∧
      (T₃.mids (((1, 1), (1, 1)), ((1, 1), (1, 1)))).card = 104416 ∧
      -- the scores
      score T₁ (Fin 5 × Fin 5) = score fiveTensor (Fin 5) + Real.log 2 / (25 * Real.log 5) ∧
      |score T₁ (Fin 5 × Fin 5) - 0.1894977| ≤ 5e-8 ∧
      score T₂ ((Fin 5 × Fin 5) × (Fin 5 × Fin 5)) =
        score T₁ (Fin 5 × Fin 5) + Real.log (184 / 64) / (625 * Real.log 25) ∧
      |score T₂ ((Fin 5 × Fin 5) × (Fin 5 × Fin 5)) - 0.1900226| ≤ 5e-8 ∧
      score T₃ (((Fin 5 × Fin 5) × (Fin 5 × Fin 5)) × ((Fin 5 × Fin 5) × (Fin 5 × Fin 5))) =
        score T₂ ((Fin 5 × Fin 5) × (Fin 5 × Fin 5)) +
          Real.log (104416 / 33856) / (390625 * Real.log 625) ∧
      |score T₃ (((Fin 5 × Fin 5) × (Fin 5 × Fin 5)) × ((Fin 5 × Fin 5) × (Fin 5 × Fin 5))) - 0.1900231| ≤
        5e-8 := by sorry

end MatMulDS
