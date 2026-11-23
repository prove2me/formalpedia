-- Prove2me | Theorems.Thm_LeJEPAWorldModel_optimal_latent_planning
-- name    : LeJEPAWorldModel.optimal_latent_planning
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:23:52.054749+00:00
-- url     : https://prove2.me/theorems/aac65d37-9c58-4230-9984-69f881af0870
-- title:
--   Theorem 4: optimal latent planning
-- statement:
--   Let $Q\in O(N)$ and let $h(z)=Qz$. Consider a finite-horizon control problem on $\mathbb R^N$ with:
--
--   1. actions in a set $\mathcal A$;
--   2. transition probabilities $P(z,a)$ that are measurable in $z$;
--   3. a stage cost $\ell(z,a)$ and a terminal cost $\ell_T(z)$, both measurable in $z$.
--
--   Assume the costs are rotation-invariant:
--
--   $$\ell(Rz,a)=\ell(z,a),\qquad\ell_T(Rz)=\ell_T(z)\qquad\text{for all }R\in O(N).$$
--
--   Let the learned-latent problem have state $\hat z=h(z)$, transitions $\hat P(\hat z,a)$ equal to the image under $h$ of $P(h^{-1}(\hat z),a)$, and the same costs. Then for every horizon $T$ and every initial state $z_0$, the two problems have the same value,
--
--   $$\hat V^*\big(h(z_0)\big)=V^*(z_0),$$
--
--   and the same optimal plans: a plan $a_{1:T}$ is optimal for the learned problem from $h(z_0)$ if and only if it is optimal for the true problem from $z_0$.
--
--   Plans computed in the learned latent are therefore the plans of the true world.
--
--   **Formalization Note** The paper writes $\hat a^*_{1:T}(h(z_0))=a^*_{1:T}(z_0)$. Optimal plans need not be unique, so the Lean statement says that the two sets of optimal plans coincide, which is what the proof establishes. The value is the infimum of the expected cost over open-loop plans of length $T$.
-- source:
--   Klindt, LeCun and Balestriero, When Does LeJEPA Learn a World Model?, arXiv:2605.26379v2 (2026), Section 4.4, Theorem 4, eq. (6), p. 6; restated and proved in Appendix D, eqs. (53)-(55), p. 26

import Mathlib
import Definitions.Def_LeJEPAWorldModel_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeJEPAWorldModel

theorem optimal_latent_planning {N : ℕ} {A : Type*} (Q : Matrix (Fin N) (Fin N) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin N) ℝ)
    (P : (Fin N → ℝ) → A → Measure (Fin N → ℝ)) (hP : ∀ z a, IsProbabilityMeasure (P z a))
    (hPmeas : ∀ a s, MeasurableSet s → Measurable fun z => P z a s)
    (c : (Fin N → ℝ) → A → ℝ) (cT : (Fin N → ℝ) → ℝ)
    (hc : ∀ a, Measurable fun z => c z a) (hcT : Measurable cT)
    (hinv : ∀ R ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∀ z a, c (R.mulVec z) a = c z a)
    (hinvT : ∀ R ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∀ z, cT (R.mulVec z) = cT z)
    (T : ℕ) (z0 : Fin N → ℝ) :
    optimalValue (pushDynamics Q P) c cT T (Q.mulVec z0) = optimalValue P c cT T z0 ∧
    ∀ as : List A, IsOptimalPlan (pushDynamics Q P) c cT T (Q.mulVec z0) as ↔
      IsOptimalPlan P c cT T z0 as := by sorry

end LeJEPAWorldModel
