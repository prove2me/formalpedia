-- Prove2me | Theorems.Thm_IteratedLP_Gaussian_theorem_3_6
-- name    : IteratedLP.Gaussian.theorem_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:21:29.297965+00:00
-- url     : https://prove2.me/theorems/29e836e1-0f04-4067-b159-50bc648c8aa2
-- title:
--   Theorem 3.6 — Talagrand's Gaussian transportation inequality $W_2^2(P,Q)\le2\sigma^2\,\mathrm{Ent}(P\mid Q)$ on an affine subspace
-- statement:
--   Let $E$ be a linear subspace of a Euclidean space $V$, let $m\in V$ and $\sigma>0$, and let $Q=N(m,\sigma^2I_E)$ be the isotropic Gaussian law on the affine subspace $m+E$. Then every probability measure $P$ on $m+E$ satisfies
--   $$W_2^2(P,Q)\le2\sigma^2\,\mathrm{Ent}(P\mid Q),$$
--   where $\mathrm{Ent}(P\mid Q)=\int\log\frac{dP}{dQ}\,dP$ if $P\ll Q$ and $+\infty$ otherwise, and $W_2$ is taken with respect to the Euclidean norm of $V$.
--
--   The paper applies it with matrices and the Frobenius norm to turn a relative-entropy bound into a coupling between the history-conditioned and the Gaussian matrix laws.
--
--   Differences from the source:
--
--   - encoding: a Euclidean space → any finite-dimensional real inner product space V (Borel σ-algebra); reason: every such space is isometric to some ℝ^d; it includes matrices with the Frobenius norm, as the paper uses it
--   - encoding: Q = N(m, σ² I_E), the isotropic Gaussian law on m + E → the image of Mathlib's standard Gaussian on E under e ↦ m + σe, with σ > 0; reason: the isotropic Gaussian on m + E is nondegenerate there; σ = 0 is excluded because the right side 0 · ∞ is not the paper's quantity
--   - encoding: Ent(P | Q); P a probability measure on the subspace → InformationTheory.klDiv P Q; P(V ∖ (m + E)) = 0; reason: for probability measures klDiv equals ∫ log(dP/dQ) dP when P ≪ Q (+∞ when that integral diverges) and +∞ otherwise
--   - encoding: W₂²(P, Q) → W2sq P Q, the published transport cost with cost ‖x − y‖² (ENNReal), multiplied against ENNReal.ofReal (2σ²); reason: same quantity in [0, ∞]
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, p. 15, Theorem 3.6 (relative entropy defined in §3.3)

import Mathlib
import Definitions.Def_IteratedLP_Gaussian_Model

open MeasureTheory ProbabilityTheory

namespace IteratedLP.Gaussian

/-- Theorem 3.6 (Gaussian transportation inequality, p. 15). Let `V` be a Euclidean space
(finite-dimensional real inner product space), `E ⊆ V` a linear subspace, `m ∈ V`, `σ > 0`, and
`Q = N(m, σ² I_E)` the isotropic Gaussian law on the affine subspace `m + E` (the image of the
standard Gaussian of `E` under `e ↦ m + σ e`). Then every probability measure `P` on `m + E`
satisfies `W₂²(P, Q) ≤ 2σ² Ent(P | Q)`, where `Ent` is the relative entropy (`+∞` unless
`P ≪ Q`). -/
theorem theorem_3_6 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (E : Submodule ℝ V) (m : V) (σ : ℝ) (hσ : 0 < σ)
    (P : Measure V) [IsProbabilityMeasure P] (hP : P {x | x - m ∉ E} = 0) :
    W2sq P ((stdGaussian E).map (fun e : E => m + σ • (e : V))) ≤
      ENNReal.ofReal (2 * σ ^ 2) *
        InformationTheory.klDiv P ((stdGaussian E).map (fun e : E => m + σ • (e : V))) := by sorry

end IteratedLP.Gaussian
