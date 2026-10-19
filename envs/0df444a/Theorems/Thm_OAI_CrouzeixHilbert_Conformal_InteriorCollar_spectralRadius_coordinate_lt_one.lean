-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_Conformal_InteriorCollar_spectralRadius_coordinate_lt_one
-- name    : OAI.CrouzeixHilbert.Conformal.InteriorCollar.spectralRadius_coordinate_lt_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:43:14.688898+00:00
-- url     : https://prove2.me/theorems/61c0408e-8492-4749-92e7-d4f44335d792
-- title:
--   The interior conformal coordinate of an operator with numerical range in a collared domain has spectral radius below 1 (OpenAI complete Crouzeix theorem)
-- statement:
--   Let $U \subseteq \mathbb C$ and let `R : InteriorCollar U` be an interior collar of $U$ (definitions bundle `OAIQWCH000`): an open set $\Omega \supseteq \overline U$ (`R.domain`) and a map $f$ (`R.f`), analytic and injective on $\Omega$, mapping $U$ onto the open unit disc and $\overline U$ onto the closed unit disc, with an analytic inverse on a disc of radius greater than $1$.
--
--   Let $H$ be a nontrivial complex Hilbert space (`InnerProductSpace ℂ H`, `CompleteSpace H`, `Nontrivial H`) and $A$ a bounded operator on $H$ whose closed numerical range lies in $U$ (`numericalClosure A ⊆ U`). Then the holomorphic functional calculus $f(A)$ (`holomorphicEval A R.domain R.f`, from the published bundle `Def_CrouzeixHilbert`) has spectral radius less than $1$:
--   $$\rho\bigl(f(A)\bigr) < 1 .$$
--   In Lean the spectral radius is Mathlib's `spectralRadius ℂ`, a value in $[0, \infty]$.
--
--   Lean: `OAI.CrouzeixHilbert.Conformal.InteriorCollar.spectralRadius_coordinate_lt_one`, OpenAI's lemma of that name (in `lean/OAI/Analysis/Crouzeix/MetricBoundary.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf, Theorem 1.2; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/MetricBoundary.lean (declaration OAI.CrouzeixHilbert.Conformal.InteriorCollar.spectralRadius_coordinate_lt_one)

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.InteriorCollar

variable {U : Set ℂ} (R : InteriorCollar U)

lemma spectralRadius_coordinate_lt_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (A : Operator H) (hKU : numericalClosure A ⊆ U) :
    spectralRadius ℂ (holomorphicEval A R.domain R.f) < 1 := by
  sorry

end Conformal.InteriorCollar

end CrouzeixHilbert

end

end OAI
end
