-- Prove2me | Theorems.Thm_LearningBasedRO_lemma_2
-- name    : LearningBasedRO.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:55.511585+00:00
-- url     : https://prove2.me/theorems/3cf2cf57-dc51-43ef-b9bc-5f66243eb1cd
-- title:
--   Lemma 2 — under (3), RO-feasible solutions are CCP-feasible with confidence $1-\delta$
-- statement:
--   Let $P$ be a measure on a measurable space $E$, let the data $D$ take values in a measurable space with law $P_D$, and let $U(D)\subseteq E$ be a data-driven uncertainty set satisfying (3):
--   $$P_D\big(P(\xi\in U(D))\ge 1-\epsilon\big)\ge 1-\delta .$$
--   Then, with $P_D$-probability at least $1-\delta$, every decision $x$ that is feasible for the robust program (2) with $U(D)$ is feasible for the chance-constrained program (1):
--   $$P_D\Big(\forall x:\ \big(g(x;\xi)\in A\ \ \forall\xi\in U(D)\big)\Rightarrow P(g(x;\xi)\in A)\ge 1-\epsilon\Big)\ge 1-\delta .$$
--
--   Lemma 2 turns a coverage statement about the set $U(D)$ into a feasibility statement about the decisions computed from it; Theorem 1 combines it with the coverage proof.
--
--   Differences from the source:
--   - generalization: an i.i.d. data set with law P_D, P a probability distribution, ϵ and δ levels → any data space with any measure μD, P any measure on any measurable space, ϵ and δ any reals, probabilities of possibly non-measurable events read as outer measures; reason: the argument is monotonicity, and the Lean statement specializes to the paper's setting
--   - generalization: any feasible solution of (2) is feasible for (1) with confidence 1 − δ → one event of probability ≥ 1 − δ on which every feasible solution of (2) is feasible for (1); reason: uniform in x, so it specializes to any (possibly data-dependent) solution
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, Lemma 2, p.6, with (3), p.5

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

namespace LearningBasedRO

/-- **Lemma 2.** If the data-driven set `U(D)` satisfies (3), then with probability at least
`1 - δ` over the data, every feasible solution of (2) using `U(D)` is feasible for (1).
Hong–Huang–Lam, arXiv:1704.04342v2, Lemma 2, p.6, with (3), p.5.

**Formalization Note** The data space `ΩD` and its law `μD` are arbitrary (the page: the i.i.d.
sample and its law); `P` is any measure and `ϵ, δ` any reals. The event is the set of data on
which every RO-feasible decision is CCP-feasible; `μD` of it is its outer measure, and the
hypothesis (3) is also read with outer measure, so no measurability is assumed. -/
theorem lemma_2 {X E Ω ΩD : Type*} [MeasurableSpace E] [MeasurableSpace ΩD]
    (P : Measure E) (μD : Measure ΩD) (g : X → E → Ω) (A : Set Ω) (ϵ δ : ℝ)
    (U : ΩD → Set E) (hU : SatisfiesReq3 μD P ϵ δ U) :
    ENNReal.ofReal (1 - δ) ≤
      μD {D | ∀ x : X, ROFeasible g A (U D) x → CCPFeasible P g A ϵ x} := by sorry

end LearningBasedRO
