-- Prove2me | Theorems.Thm_LargeDelaySGD_MeanSquare_Supplement_lemma_4
-- name    : LargeDelaySGD.MeanSquare.Supplement.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T08:08:02.676802+00:00
-- url     : https://prove2.me/theorems/63c050a2-963e-46ef-ac92-91c341afd9da
-- title:
--   Lemma 4, p. 14 — ‖pr_X(y) − ŷ‖² − ‖pr_X(ŷ) − ŷ‖² ≤ ‖y − ŷ‖² and E_{x*}(y + Δy) − E_{x*}(y) ≤ 2⟨Δy, pr_X(y) − x*⟩ + ‖Δy‖²
-- statement:
--   Throughout, $\mathcal X\subseteq\mathbb R^d$ is a nonempty compact convex feasible set, $F(x;\omega)$ a random function with $f(x)=\mathbb E[F(x;\omega)]$, $\nabla f(x)=\mathbb E[\nabla F(x;\omega)]$ on $\mathcal X$, $\mathcal X^*$ the set of minimizers of $f$ over $\mathcal X$, and $\mathrm{pr}_{\mathcal X}$ the Euclidean projection onto $\mathcal X$. Assumption 1 is imposed on $\mathcal X$ only, Assumption 3 is mean variational coherence, and Assumption 4 is the printed implication $E(y_n)\to0\Rightarrow\mathrm{pr}_{\mathcal X}(y_n)\to\mathcal X^*$. A sequence converges to $\mathcal X^*$ when its distance to $\mathcal X^*$ tends to $0$.
--
--   **Lemma 4.** Fix any $x^*\in\mathcal X^*$.
--
--   1. For all $y,\hat y\in\mathbb R^d$,
--   $$\|\mathrm{pr}_{\mathcal X}(y)-\hat y\|_2^2-\|\mathrm{pr}_{\mathcal X}(\hat y)-\hat y\|_2^2\le\|y-\hat y\|_2^2 .$$
--   2. For all $y,\Delta y\in\mathbb R^d$,
--   $$E_{x^*}(y+\Delta y)-E_{x^*}(y)\le2\langle\Delta y,\mathrm{pr}_{\mathcal X}(y)-x^*\rangle+\|\Delta y\|_2^2 .$$
--
--   Part 2 is the one-step energy bound that the proofs of Propositions 1–2 and Theorem 2 telescope along the iterates; part 1 is the projection inequality behind it.
--
--   Differences from the source:
--   - generalization: Lemma 4 inside §4, under Assumptions 1–4 → only X nonempty compact convex and x* ∈ X*; no Assumption 1–4 and an arbitrary measure μ; reason: both inequalities are statements about the projection onto a closed convex set and hold for every x*; adding the assumptions specializes to the source
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1 (SHA-256 20dd663845757ad1e06f51c4ae62f8fd6623aa921b66be496b00befa51d9a327), p. 14, Lemma 4 (proof App. B.2.2, p. 28)

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model
import Definitions.Def_SolodovSvaiterVI_Alg21_projOnto
import Definitions.Def_LargeDelaySGD_MeanSquare_Supplement_Constrained

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace LargeDelaySGD.MeanSquare.Supplement

theorem lemma_4 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X) (hXne : X.Nonempty) :
    (∀ y yh : EuclideanSpace ℝ (Fin d),
      ‖proj X y - yh‖ ^ 2 - ‖proj X yh - yh‖ ^ 2 ≤ ‖y - yh‖ ^ 2) ∧
    ∀ xs ∈ solutionSet F μ X, ∀ y Δy : EuclideanSpace ℝ (Fin d),
      energyAt X xs (y + Δy) - energyAt X xs y ≤
        2 * inner ℝ Δy (proj X y - xs) + ‖Δy‖ ^ 2 := by sorry

end LargeDelaySGD.MeanSquare.Supplement
