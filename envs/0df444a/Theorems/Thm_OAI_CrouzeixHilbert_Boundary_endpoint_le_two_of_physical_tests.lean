-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_Boundary_endpoint_le_two_of_physical_tests
-- name    : OAI.CrouzeixHilbert.Boundary.endpoint_le_two_of_physical_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:40:14.084868+00:00
-- url     : https://prove2.me/theorems/e37d5dc9-3f2b-411d-aba4-b96f0f1a0958
-- title:
--   The optimal similarity constant is at most 2 when the boundary densities pass the Laurent tests (OpenAI complete Crouzeix theorem)
-- statement:
--   All definitions are from the definitions bundle `OAIQWCH000`, except `Coeff`, `Amplification` and `Operator` from the published bundle `Def_CrouzeixHilbert`. Let $\mathbb T = \mathbb R/\mathbb Z$ (`CircleSpace`) with normalized Haar measure $\sigma$ (`circleMeasure`), and let $L^2_n$ (`BoundaryL2 n`) be the space of square-integrable $M_n(\mathbb C)$-valued functions on $\mathbb T$ with the Hilbert–Schmidt norm. For a real-linear operator $M$ on $L^2_n$, `boundaryCauchy M` is $P_0 + P_+ + P_- M P_+$, where $P_0, P_+, P_-$ are the projections onto the zero, positive and negative Fourier modes; `lpStar` is the pointwise adjoint $u \mapsto u^*$. `boundaryField V` is a continuous field $V : \mathbb T \to M_n(\mathbb C)$ as an element of $L^2_n$; `matrixLaurentMonomial (j, (a, b)) c` is $t \mapsto c\, e^{2\pi i j t} E_{ab}$; `tensorIntegral E V` is $\int_{\mathbb T} E(t) \otimes V(t)\, d\sigma$ on $\mathbb C^n \otimes \mathbb C^n$; and `vectorization X` is $\operatorname{vec} X = \sum_j X e_j \otimes e_j$. For a continuous $F : \mathbb T \to M_n(\mathbb C)$ with $\|F(t)\| \le 1$, `lpLeft F _ _` and `lpRight F _ _` are the operators of pointwise left and right multiplication by $F$ on $L^2_n$.
--
--   **Statement.** Let $M$ be a real-linear operator on $L^2_n$ with $\|M\| \le 1$. Let $E, \Lambda, F : \mathbb T \to M_n(\mathbb C)$ be continuous, with $E(t)$ and $\Lambda(t)$ positive semidefinite for every $t$, $\int_{\mathbb T} \Lambda\, d\sigma = I$ (`circleMeasure`), and $\|F(t)\| \le 1$ for every $t$. Suppose $C = $ `boundaryCauchy M` satisfies $C\,\ell_F\,C = \ell_F\,C$ and $C\,r_F\,C = r_F\,C$, where $\ell_F$, $r_F$ are `lpLeft F` and `lpRight F`. Let $S$ be a self-adjoint operator on $\mathbb C^n \otimes \mathbb C^n$, let $X, Y \in M_n(\mathbb C)$ with $\|\operatorname{vec} X\| = \|\operatorname{vec} Y\| = 1$ and $X^* Y = 0$, and let $\kappa > 0$ with $S \operatorname{vec} X = \kappa \operatorname{vec} X$, $S \operatorname{vec} Y = \operatorname{vec} Y$ and $\bigl(\int \Lambda \otimes F\bigr)\operatorname{vec} X = \operatorname{vec} Y$. Suppose finally that the Laurent tests hold for $M$, $E$, $\Lambda$ and $S$: for every Laurent monomial $\mu$ there are $V, W, B, L$ with $C\mu = V$, $C\mu^* = W$, $\int E \otimes \mu = B + L^*$, $SB = (\int \Lambda \otimes V) S$ and $SL = (\int \Lambda \otimes W) S$. Then
--   $$\kappa \le 2 .$$
--
--   Lean: `OAI.CrouzeixHilbert.Boundary.endpoint_le_two_of_physical_tests`, OpenAI's theorem of that name (in `lean/OAI/Analysis/Crouzeix/PhysicalComparison.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf, Sections 4–5; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/PhysicalComparison.lean (declaration OAI.CrouzeixHilbert.Boundary.endpoint_le_two_of_physical_tests)

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

theorem endpoint_le_two_of_physical_tests {n : ℕ}
    (M : BoundaryL2 n →L[ℝ] BoundaryL2 n) (hM : ‖M‖ ≤ 1)
    (E Λ F : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) (hΛ : ∀ t, (Λ t).PosSemidef)
    (hmass : ∫ t, Λ t ∂circleMeasure = 1) (hF : ∀ t, ‖F t‖ ≤ 1)
    (hleft : (boundaryCauchy M).comp
        ((lpLeft F F.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall hF)).comp (boundaryCauchy M)) =
      (lpLeft F F.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hF)).comp (boundaryCauchy M))
    (hright : (boundaryCauchy M).comp
        ((lpRight F F.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall hF)).comp (boundaryCauchy M)) =
      (lpRight F F.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hF)).comp (boundaryCauchy M))
    (S : Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)) (hS : IsSelfAdjoint S)
    (X Y : Coeff n) (hX : ‖vectorization X‖ = 1) (hY : ‖vectorization Y‖ = 1)
    (hXY : Xᴴ * Y = 0) (κ : ℝ) (hκ : 0 < κ)
    (hx : S (vectorization X) = (κ : ℂ) • vectorization X)
    (hy : S (vectorization Y) = vectorization Y)
    (hI : tensorIntegral Λ F (vectorization X) = vectorization Y)
    (htest : ∀ (j : ℤ × (Fin n × Fin n)) (c : ℂ),
      ∃ (V W : C(CircleSpace, Coeff n))
        (B L : Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)),
        boundaryCauchy M (boundaryField (matrixLaurentMonomial j c)) = boundaryField V ∧
        boundaryCauchy M (lpStar (boundaryField (matrixLaurentMonomial j c))) =
          boundaryField W ∧
        tensorIntegral E (matrixLaurentMonomial j c) = B + L.adjoint ∧
        S * B = tensorIntegral Λ V * S ∧ S * L = tensorIntegral Λ W * S) :
    κ ≤ 2 := by
  sorry

end CrouzeixHilbert.Boundary

end

end OAI
end
