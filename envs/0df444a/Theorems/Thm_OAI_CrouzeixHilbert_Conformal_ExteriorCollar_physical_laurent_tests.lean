-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_Conformal_ExteriorCollar_physical_laurent_tests
-- name    : OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_laurent_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:43:34.939033+00:00
-- url     : https://prove2.me/theorems/7eb62a58-2946-4abd-94d1-6be5d7553e50
-- title:
--   The resolvent boundary density of a matrix passes the Laurent tests for the boundary kernel operator (OpenAI complete Crouzeix theorem)
-- statement:
--   The setting is that of the published statement `OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_channel_intertwines`: $U$ open and convex with collars `C : ExteriorCollar U` and `R : InteriorCollar U`; $n \ge 1$; $A, D, S$ operators on $\mathbb C^n$ with the closed numerical range of $A$ in $U$, $\|D\| \le 1$, $\rho(D) < 1$ and $S f(A) = D S$. The boundary notation (`boundaryCauchy`, `boundaryField`, `lpStar`, `matrixLaurentMonomial`, `tensorIntegral`) is that of the published statement `OAI.CrouzeixHilbert.Boundary.endpoint_le_two_of_physical_tests`. All definitions are from the definitions bundle `OAIQWCH000`.
--
--   `C.boundaryOperator hc n` is the integral operator on $L^2_n$ with the nonnegative kernel $1 + 2\operatorname{Re} c(s, t)$ built from the exterior map (`C.boundaryKernel`), whose integrals in each variable are $1$; `C.matrixResolventDensity A hKU hU` is $\Theta + \Theta^*$, pointwise, for the matrix resolvent density $\Theta$ of $A$ along the boundary curve (`C.matrixResolvent`); and `C.matrixDensity R D hD` is the matrix density of the published statement `physical_channel_intertwines`.
--
--   **Statement.** For every $a \in \mathbb Z \times (\mathrm{Fin}\,n \times \mathrm{Fin}\,n)$ and $c \in \mathbb C$, writing $\mu$ = `matrixLaurentMonomial a c`, $K$ = `boundaryCauchy (C.boundaryOperator hc n)`, $E$ = `C.matrixResolventDensity A hKU hU` and $\Lambda$ = `C.matrixDensity R D hD`, there are continuous fields $V, W : \mathbb T \to M_n(\mathbb C)$ and operators $B, L$ on $\mathbb C^n \otimes \mathbb C^n$ with
--   $$K\mu = V,\quad K\mu^* = W,\quad \int E \otimes \mu = B + L^*,\quad (S \otimes I)B = \Bigl(\int \Lambda \otimes V\Bigr)(S \otimes I),\quad (S \otimes I)L = \Bigl(\int \Lambda \otimes W\Bigr)(S \otimes I).$$
--
--   Lean: `OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_laurent_tests`, OpenAI's lemma of that name (in `lean/OAI/Analysis/Crouzeix/BoundaryMoments.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf, Section 5; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/BoundaryMoments.lean (declaration OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_laurent_tests)

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

lemma physical_laurent_tests (hc : Convex ℝ U)
    (D S : Operator (EuclideanSpace ℂ (Fin n)))
    (hN : ‖D‖ ≤ 1) (hD : spectralRadius ℂ D < 1)
    (hI : S * holomorphicEval A R.domain R.f = D * S)
    (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    ∃ (V W : C(CircleSpace, Coeff n))
      (B L : Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)),
      boundaryCauchy (C.boundaryOperator hc n) (boundaryField (matrixLaurentMonomial a c)) = boundaryField V ∧
      boundaryCauchy (C.boundaryOperator hc n) (lpStar (boundaryField (matrixLaurentMonomial a c))) = boundaryField W ∧
      tensorIntegral (C.matrixResolventDensity A hKU hU) (matrixLaurentMonomial a c) = B + L.adjoint ∧
      tensorOperator S (1 : Coeff n) * B =
        tensorIntegral (C.matrixDensity R D hD) V * tensorOperator S (1 : Coeff n) ∧
      tensorOperator S (1 : Coeff n) * L =
        tensorIntegral (C.matrixDensity R D hD) W * tensorOperator S (1 : Coeff n) := by
  sorry

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end
