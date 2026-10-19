-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_matrixHolomorphicEval_matrixRationalFunction
-- name    : OAI.CrouzeixHilbert.matrixHolomorphicEval_matrixRationalFunction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:34:30.885986+00:00
-- url     : https://prove2.me/theorems/2b0ba07d-2d29-4cf1-950f-e6120eb4dcee
-- title:
--   Holomorphic and rational functional calculus agree for matrix-valued rational functions with poles outside the domain (OpenAI complete Crouzeix theorem)
-- statement:
--   All definitions are those of the published bundle `Def_CrouzeixHilbert`. Let $H$ be a nontrivial complex Hilbert space and $A$ a bounded operator on $H$. Let $U \subseteq \mathbb C$ and suppose there is a calculus contour `Γ : CalculusContour (numericalClosure A) U` for the closed numerical range of $A$ in $U$: a smooth closed contour in $U$ avoiding the closed numerical range, with winding number $1$ about each of its points and $0$ about each point outside $U$. Let $m$ be a natural number and $R$ an $m \times m$ matrix of rational functions (`RationalMatrix m`) whose poles all lie outside $U$ (`PolesOutside U R`). Then
--   $$R[A]_{\mathrm{hol}} \;=\; R[A]_{\mathrm{rat}},$$
--   where the left side is the holomorphic functional calculus of the matrix function $z \mapsto R(z)$ (`matrixHolomorphicEval A U (matrixRationalFunction R)`) and the right side is the rational functional calculus (`matrixRationalEval A R`, numerator polynomials of $A$ times inverses of denominator polynomials of $A$).
--
--   Lean: `OAI.CrouzeixHilbert.matrixHolomorphicEval_matrixRationalFunction`, OpenAI's theorem of that name (in `lean/OAI/Analysis/Crouzeix/RationalContours.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/RationalContours.lean (declaration OAI.CrouzeixHilbert.matrixHolomorphicEval_matrixRationalFunction)

import Mathlib
import Definitions.Def_CrouzeixHilbert

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProductSpace Topology TensorProduct Matrix.Norms.L2Operator

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem matrixHolomorphicEval_matrixRationalFunction [CompleteSpace H] [Nontrivial H]
    (A : Operator H) {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {m : ℕ} (R : RationalMatrix m) (hR : PolesOutside U R) :
    matrixHolomorphicEval A U (matrixRationalFunction R) = matrixRationalEval A R := by
  sorry

end CrouzeixHilbert

end

end OAI
end
