-- Prove2me | Theorems.Thm_LaarakkerOttenVanDenBerg2026_propositions_2_and_3
-- name    : LaarakkerOttenVanDenBerg2026.propositions_2_and_3
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T15:42:16.298218+00:00
-- url     : https://prove2.me/theorems/24e3bce8-fdf3-4db7-a6f9-645856ad2175
-- title:
--   Propositions 2 & 3: Definable Quantifier Swapping and Fixed-Type Quantifier Equivalences
-- statement:
--   **Propositions 2 & 3 (Section 2.3, pp. 7–8)**:
--   1. **Proposition 2 (p. 7)**: For all small types $A : U$ and $x : \mathrm{El}\,A, i : \mathsf{Size} \vdash B(x, i) : U$, the definable quantifier-swapping maps `swapPiAll` ($\Pi x : A.\,\forall i.\,B(x, i) \to \forall i.\,\Pi x : A.\,B(x, i)$) and `swapSigmaEx` ($\Sigma x : A.\,\exists i.\,B(x, i) \to \exists i.\,\Sigma x : A.\,B(x, i)$) are half-adjoint equivalences with explicit inverses `unswapPiAll` and `unswapSigmaEx`.
--   2. **Proposition 3 (p. 8)**: In any `ParametricSizeTheory`, for every size-independent small type $A : U$, the canonical maps `constExToEl` ($\exists i.\,A \to A$) and `elToConstAll` ($A \to \forall i.\,A$) are half-adjoint equivalences.
-- source:
--   Bastiaan Laarakker, Daniël Otten, and Benno van den Berg, 'Constructing (Co)inductive Types via Large Sizes', FSCD 2026 (arXiv:2602.18921), Section 2.3, Propositions 2 & 3 (pp. 7–8)

import Definitions.Def_LaarakkerOttenVanDenBerg2026_TypeTheory

namespace LaarakkerOttenVanDenBerg2026

universe u v

theorem propositions_2_and_3
    (P : ParametricSizeTheory.{u, v}) :
    (∀ (A : P.U) (B : P.El A → P.Size → P.U),
      (∀ f, P.unswapPiAll A B (P.swapPiAll A B f) = f) ∧
      (∀ g, P.swapPiAll A B (P.unswapPiAll A B g) = g) ∧
      Nonempty (IsHAEquiv (P.swapPiAll A B)) ∧
      (∀ p, P.unswapSigmaEx A B (P.swapSigmaEx A B p) = p) ∧
      (∀ q, P.swapSigmaEx A B (P.unswapSigmaEx A B q) = q) ∧
      Nonempty (IsHAEquiv (P.swapSigmaEx A B))) ∧
    (∀ (A : P.U),
      Nonempty (IsHAEquiv (P.constExToEl A)) ∧
      Nonempty (IsHAEquiv (P.elToConstAll A))) := by
  sorry

end LaarakkerOttenVanDenBerg2026
