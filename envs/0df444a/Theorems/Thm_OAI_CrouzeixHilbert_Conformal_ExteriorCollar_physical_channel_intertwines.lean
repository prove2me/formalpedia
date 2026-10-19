-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_Conformal_ExteriorCollar_physical_channel_intertwines
-- name    : OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_channel_intertwines
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:40:22.183608+00:00
-- url     : https://prove2.me/theorems/d76358a4-7505-4496-b9e1-1f8515ea8de0
-- title:
--   The boundary representation for the physical Laurent channels of a matrix (OpenAI complete Crouzeix theorem)
-- statement:
--   The setting is that of the published statement `OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_intertwines`, for a matrix: $U$ open and convex with collars `C : ExteriorCollar U` and `R : InteriorCollar U`; $n \ge 1$ (`Nonempty (Fin n)`); $A, D, S$ operators on $\mathbb C^n$ with the closed numerical range of $A$ in $U$, $\|D\| \le 1$, $\rho(D) < 1$ and $S f(A) = D S$ for $f$ = `R.f`. All definitions are from the definitions bundle `OAIQWCH000`.
--
--   For $j \in \mathbb Z$ and $z \in \mathbb C$, `C.physicalCoefficient j z` is $\int_{\mathbb T} (2e(t))^j \,\frac{2e(t)\,G'(2e(t))}{G(2e(t)) - z}\,d\sigma(t)$ with $e(t) = e^{2\pi i t}$. For $a = (j, (k, l))$ and $c \in \mathbb C$, `C.physicalRepresentative a c z` is the matrix $c\,\text{physicalCoefficient}(j, z)\,E_{kl}$, holomorphic on the outer domain `C.outerDomain` (the complement of the closed curve $t \mapsto G(2e(t))$), and `C.physicalChannel a` is the continuous field $t \mapsto \text{physicalCoefficient}(j, G(e(t)))\,E_{kl}$. `C.matrixDensity R D hD` is the matrix form of the operator density `C.operatorDensity R D hD`.
--
--   **Statement.**
--   $$(S \otimes I_n)\; \text{physicalRepresentative}(a, c)[A] \;=\; \Bigl(\int_{\mathbb T} \text{matrixDensity}(t) \otimes c\,\text{physicalChannel}(a)(t)\, d\sigma(t)\Bigr)\,(S \otimes I_n),$$
--   where the left evaluation is `matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative a c)` and the right integral is `tensorIntegral (C.matrixDensity R D hD) (c • C.physicalChannel a)`.
--
--   Lean: `OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_channel_intertwines`, OpenAI's lemma of that name (in `lean/OAI/Analysis/Crouzeix/BoundaryMoments.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf, Section 5; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/BoundaryMoments.lean (declaration OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_channel_intertwines)

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

variable {U : Set ℂ} (C : ExteriorCollar U)

variable {n : ℕ} (A : Operator (EuclideanSpace ℂ (Fin n)))
    (hKU : numericalClosure A ⊆ U) (hU : IsOpen U)

variable [Nonempty (Fin n)]

variable (R : InteriorCollar U)

include hKU hU in
lemma physical_channel_intertwines (hc : Convex ℝ U)
    (D S : Operator (EuclideanSpace ℂ (Fin n)))
    (hN : ‖D‖ ≤ 1) (hD : spectralRadius ℂ D < 1)
    (hI : S * holomorphicEval A R.domain R.f = D * S)
    (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    tensorOperator S (1 : Coeff n) *
        matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative a c) =
      tensorIntegral (C.matrixDensity R D hD) (c • C.physicalChannel a) *
        tensorOperator S (1 : Coeff n) := by
  sorry

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end
