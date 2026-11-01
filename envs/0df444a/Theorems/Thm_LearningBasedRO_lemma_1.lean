-- Prove2me | Theorems.Thm_LearningBasedRO_lemma_1
-- name    : LearningBasedRO.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:52.146551+00:00
-- url     : https://prove2.me/theorems/9d000304-9780-4237-b0c0-7c694edc918e
-- title:
--   Lemma 1 — RO-feasible with a $(1-\epsilon)$-content set implies CCP-feasible
-- statement:
--   Let $P$ be a measure on a measurable space $E$, $g:X\times E\to\Omega$, $A\subseteq\Omega$ and $\epsilon\in\mathbb R$. Let $U\subseteq E$ be a $(1-\epsilon)$-content set, $P(\xi\in U)\ge 1-\epsilon$. If $x$ is feasible for the robust program (2) with uncertainty set $U$, that is $g(x;\xi)\in A$ for all $\xi\in U$, then $x$ is feasible for the chance-constrained program (1):
--   $$P\big(g(x;\xi)\in A\big)\ge 1-\epsilon .$$
--
--   This is the reason a robust program with a high-content uncertainty set is a safe approximation of a chance constraint, and the first link in the guarantee of Theorem 1.
--
--   Differences from the source:
--   - generalization: P a probability distribution on ℝᵐ, ϵ a tolerance level, x ∈ ℝᵈ → P any measure on any measurable space, ϵ any real, X and Ω arbitrary types, P(g(x;ξ) ∈ A) the outer measure of a possibly non-measurable set; reason: the argument is monotonicity of the measure, and the Lean statement specializes to the paper's setting
--   - encoding: the objective f of (1) and (2) → omitted; reason: the lemma concerns feasibility only
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, Lemma 1, p.5

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

namespace LearningBasedRO

/-- **Lemma 1.** Any feasible solution of the robust program (2) using a `(1 - ϵ)`-content set
`U` is feasible for the chance-constrained program (1).
Hong–Huang–Lam, arXiv:1704.04342v2, Lemma 1, p.5.

**Formalization Note** `P` is any measure and `ϵ` any real (the page's `P` is a probability
distribution and `ϵ ∈ (0,1)`); `X`, `E`, `Ω` are arbitrary types (the page: `ℝᵈ`, `ℝᵐ`). -/
theorem lemma_1 {X E Ω : Type*} [MeasurableSpace E] (P : Measure E) (g : X → E → Ω)
    (A : Set Ω) (ϵ : ℝ) (U : Set E) (hU : IsContentSet P ϵ U) (x : X)
    (hx : ROFeasible g A U x) : CCPFeasible P g A ϵ x := by sorry

end LearningBasedRO
