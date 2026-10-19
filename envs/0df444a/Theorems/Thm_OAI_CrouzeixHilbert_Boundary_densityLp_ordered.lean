-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_Boundary_densityLp_ordered
-- name    : OAI.CrouzeixHilbert.Boundary.densityLp_ordered
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:39:53.05367+00:00
-- url     : https://prove2.me/theorems/997dded7-bcfb-4200-b438-7e7aa3c780e1
-- title:
--   Equality in the common positive representation orders the projected boundary densities (OpenAI complete Crouzeix theorem)
-- statement:
--   All definitions are from the definitions bundle `OAIQWCH000`, except `Coeff`, `Amplification`, `Operator` and `tensorOperator` from the published bundle `Def_CrouzeixHilbert`. Let $\mathbb T = \mathbb R/\mathbb Z$ (`CircleSpace`) with normalized Haar measure $\sigma$ (`circleMeasure`), and let $L^2_n$ (`BoundaryL2 n`) be the space of square-integrable $M_n(\mathbb C)$-valued functions on $\mathbb T$. For continuous $E : \mathbb T \to M_n(\mathbb C)$ and $X, Y \in M_n(\mathbb C)$, `densityLp E X Y` is the function $t \mapsto (X^* E(t) Y)^{\mathsf T}$ as an element of $L^2_n$, and `ofHS` reads an element of the Hilbert–Schmidt space as a matrix. `vectorization X` is $\operatorname{vec} X = \sum_j X e_j \otimes e_j \in \mathbb C^n \otimes \mathbb C^n$, `matrixOperatorMap n A` is the operator of the matrix $A$ on $\mathbb C^n$, and `tensorOperator A F` is $A \otimes F$.
--
--   **Statement.** Let $E, F : \mathbb T \to M_n(\mathbb C)$ be continuous, with $E(t)$ positive semidefinite for every $t$, $\int_{\mathbb T} E\, d\sigma = I$, and $\|F(t)\| \le 1$ for every $t$. Let $X, Y \in M_n(\mathbb C)$ with $\|\operatorname{vec} X\| = \|\operatorname{vec} Y\|$ and
--   $$\Bigl(\int_{\mathbb T} E(t) \otimes F(t)\, d\sigma(t)\Bigr) \operatorname{vec} X = \operatorname{vec} Y .$$
--   Then for $\sigma$-almost every $t$, writing $p, q, r$ for the matrices of `densityLp E X X`, `densityLp E Y Y` and `densityLp E X Y` at $t$,
--   $$p = F(t)^* \, r, \qquad r = F(t)\, p, \qquad q = r\, F(t)^* .$$
--
--   These are equations (4.4) of the paper, for the density $\Lambda$ there.
--
--   Lean: `OAI.CrouzeixHilbert.Boundary.densityLp_ordered`, OpenAI's theorem of that name (in `lean/OAI/Analysis/Crouzeix/BoundaryFibers.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf, Section 4.1, equations (4.2)–(4.4); Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/BoundaryFibers.lean (declaration OAI.CrouzeixHilbert.Boundary.densityLp_ordered)

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

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert.Boundary

theorem densityLp_ordered {n : ℕ} (E F : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) (hmass : ∫ t, E t ∂circleMeasure = 1)
    (hF : ∀ t, ‖F t‖ ≤ 1) (X Y : Coeff n)
    (hN : ‖vectorization X‖ = ‖vectorization Y‖)
    (hI : (∫ t, tensorOperator (matrixOperatorMap n (E t)) (F t)
      ∂circleMeasure) (vectorization X) = vectorization Y) :
    ∀ᵐ t ∂circleMeasure,
      ofHS (densityLp E X X t) = (F t)ᴴ * ofHS (densityLp E X Y t) ∧
      ofHS (densityLp E X Y t) = F t * ofHS (densityLp E X X t) ∧
      ofHS (densityLp E Y Y t) = ofHS (densityLp E X Y t) * (F t)ᴴ := by
  sorry

end CrouzeixHilbert.Boundary

end

end OAI
end
