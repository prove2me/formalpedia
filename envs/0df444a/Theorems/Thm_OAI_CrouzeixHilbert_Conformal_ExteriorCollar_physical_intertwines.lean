-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_Conformal_ExteriorCollar_physical_intertwines
-- name    : OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_intertwines
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:42:40.528575+00:00
-- url     : https://prove2.me/theorems/5a8c0227-7314-4293-8763-a0931c40adc0
-- title:
--   A similarity intertwining the disk coordinate gives a boundary-integral representation of matrix-valued holomorphic evaluation (OpenAI complete Crouzeix theorem)
-- statement:
--   Let $U \subseteq \mathbb C$ be open and convex, with an exterior collar `C : ExteriorCollar U` (boundary parametrization $t \mapsto G(e^{2\pi i t})$, `C.boundaryMap`) and an interior collar `R : InteriorCollar U` (conformal coordinate $f$ = `R.f` on `R.domain`), as described in the published statement `OAI.CrouzeixHilbert.Conformal.ExteriorCollar.holomorphic_bound` (definitions bundle `OAIQWCH000`). Let $H$ be a nontrivial complex Hilbert space and $A, D, S$ bounded operators on $H$ such that the closed numerical range of $A$ lies in $U$, $\|D\| \le 1$, $\rho(D) < 1$, and $S f(A) = D S$, where $f(A)$ is `holomorphicEval A R.domain R.f`.
--
--   For $t \in \mathbb T$, `C.operatorDensity R D hD t` is the operator $J(t)\,\varphi_D(\theta(t))$, where $\varphi_D$ is the disk density of the published statement `OAI.CrouzeixHilbert.Disk.integral_matrixHolomorphic`, $\theta(t)$ is the angle of $f(G(e^{2\pi i t}))$ on the unit circle (`C.interiorAngle R`), and $J$ is the corresponding change-of-variables factor (`C.angularJacobian R`).
--
--   **Statement.** Let $V$ be open with $\overline U \subseteq V$, $m$ a natural number and $F : \mathbb C \to M_m(\mathbb C)$ entrywise holomorphic on $V$. Then
--   $$(S \otimes I_m)\, F[A] \;=\; \Bigl(\int_{\mathbb T} \text{operatorDensity}(t) \otimes F\bigl(G(e^{2\pi i t})\bigr)\, d\sigma(t)\Bigr)\,(S \otimes I_m),$$
--   with $F[A]$ = `matrixHolomorphicEval A V F` and $\otimes$ = `tensorOperator` (published bundle `Def_CrouzeixHilbert`). The integral is a Bochner integral in the operators on $H \otimes \mathbb C^m$, with the real normed-space structure the statement activates as a local instance.
--
--   Lean: `OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_intertwines`, OpenAI's lemma of that name (in `lean/OAI/Analysis/Crouzeix/PhysicalCalculus.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf, Theorem 1.3; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/PhysicalCalculus.lean (declaration OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_intertwines)

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

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physicalCalculusOperatorRealNormedSpace
variable [Nontrivial H]

lemma physical_intertwines (hU : IsOpen U) (hc : Convex ℝ U)
    (A D S : Operator H) (hKU : numericalClosure A ⊆ U)
    (hN : ‖D‖ ≤ 1) (hD : spectralRadius ℂ D < 1)
    (hI : S * holomorphicEval A R.domain R.f = D * S)
    {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {m : ℕ} {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic V F) :
    tensorOperator S (1 : Coeff m) * matrixHolomorphicEval A V F =
      (∫ t, tensorOperator (C.operatorDensity R D hD t) (F (C.boundaryMap t)) ∂circleMeasure) *
        tensorOperator S (1 : Coeff m) := by
  sorry

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end
