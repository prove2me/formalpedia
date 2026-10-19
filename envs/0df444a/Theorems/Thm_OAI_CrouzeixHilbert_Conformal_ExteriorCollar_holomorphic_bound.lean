-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_Conformal_ExteriorCollar_holomorphic_bound
-- name    : OAI.CrouzeixHilbert.Conformal.ExteriorCollar.holomorphic_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:40:08.538868+00:00
-- url     : https://prove2.me/theorems/94ca4abd-f0f2-4b9a-80de-62db150b2661
-- title:
--   Constant-2 bound for matrix-valued holomorphic evaluation of a matrix whose numerical range lies in an analytic convex domain (OpenAI complete Crouzeix theorem)
-- statement:
--   Let $U \subseteq \mathbb C$ be open, convex and bounded, and suppose $U$ carries two collars (definitions bundle `OAIQWCH000`):
--   - an exterior collar `C : ExteriorCollar U`: a map $G$, analytic and injective on $\{|t| > r\}$ for some $0 < r < 1$, mapping $\{|t| > 1\}$ bijectively onto the complement of $\overline U$, the unit circle bijectively onto $\partial U$ and $\{r < |t| < 1\}$ into $U$, of the form $G(t) = \lambda t + g(1/t)$ with $\lambda \ne 0$ and $g$ analytic near $0$;
--   - an interior collar `R : InteriorCollar U`: an open set $\Omega \supseteq \overline U$ and maps $f$ (analytic and injective on $\Omega$) and $h$ (analytic and injective on a disc of radius $> 1$) that are inverse bijections between $U$ and the open unit disc and between $\overline U$ and the closed unit disc, with $|f| = 1$ on $\partial U$.
--
--   Let $n \ge 1$ and let $A$ be a complex $n \times n$ matrix, as an operator on $\mathbb C^n$, whose closed numerical range lies in $U$ (`numericalClosure A ⊆ U`). Let $V$ be an open set with $\overline U \subseteq V$, $m$ a natural number and $F : \mathbb C \to M_m(\mathbb C)$ entrywise holomorphic on $V$ (`EntrywiseHolomorphic V F`). Then
--   $$\bigl\| F[A] \bigr\| \;\le\; 2 \sup_{z \in \overline U} \|F(z)\|,$$
--   where $F[A]$ is the holomorphic functional calculus with matrix coefficients (`matrixHolomorphicEval A V F`, from the published bundle `Def_CrouzeixHilbert`) and the supremum is `supNorm (closure U) F`.
--
--   This is the constant-two bound of OpenAI's Theorems 1.2–1.3 on an analytic convex neighbourhood of the numerical range.
--
--   Lean: `OAI.CrouzeixHilbert.Conformal.ExteriorCollar.holomorphic_bound`, OpenAI's lemma of that name (in `lean/OAI/Analysis/Crouzeix/CompleteFinite.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf, Theorems 1.2–1.3; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/CompleteFinite.lean (declaration OAI.CrouzeixHilbert.Conformal.ExteriorCollar.holomorphic_bound)

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

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {n : ℕ} (hn : 0 < n) (A : Operator (EuclideanSpace ℂ (Fin n)))
    (hKU : numericalClosure A ⊆ U) (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U)

include C R hn hKU hU hc hb

lemma holomorphic_bound {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {m : ℕ} {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic V F) :
    ‖matrixHolomorphicEval A V F‖ ≤ 2 * supNorm (closure U) F := by
  sorry

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end
