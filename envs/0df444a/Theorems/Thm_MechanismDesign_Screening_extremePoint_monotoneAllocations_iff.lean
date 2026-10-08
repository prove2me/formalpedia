-- Prove2me | Theorems.Thm_MechanismDesign_Screening_extremePoint_monotoneAllocations_iff
-- name    : MechanismDesign.Screening.extremePoint_monotoneAllocations_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T22:44:41.932748+00:00
-- url     : https://prove2.me/theorems/062b4ab8-307a-4360-bf1c-d768c51bddcc
-- title:
--   Lemma 2.7 -- the extreme points of $M$ are the $\{0,1\}$-valued functions
-- statement:
--   Let $0\le\underline\theta<\bar\theta$ and let $M$ be the set of increasing functions $[\underline\theta,\bar\theta]\to[0,1]$ in $L^1([\underline\theta,\bar\theta])$. A function $q\in M$ is an extreme point of $M$ (Definition 2.4) if and only if
--   $$q(\theta)\in\{0,1\}\quad\text{for almost all }\theta\in[\underline\theta,\bar\theta],$$
--   where "almost all" means for a set of $\theta$ of Lebesgue measure $\bar\theta-\underline\theta$ (the book's note 4).
--
--   Hence the seller can restrict attention to non-stochastic mechanisms, and an increasing $\{0,1\}$-valued $q$ is a threshold rule, i.e. a posted price.
--
--   **Formalization Note** Elements of $M$ are $L^1$ classes, so "$q(\theta)\in\{0,1\}$" is evaluated on any representative, almost everywhere with respect to Lebesgue measure on $[\underline\theta,\bar\theta]$. A nonzero $y$ in Definition 2.4 is nonzero in $L^1$, i.e. nonzero on a set of positive measure, exactly as in the book's note 5.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.17, Lemma 2.7; p.235, notes 4–6 to Chapter 2

import Mathlib
import Definitions.Def_MechanismDesign_Screening_ExtremePoints

namespace MechanismDesign.Screening

/-- **Lemma 2.7**, p.17. A function `q ∈ M` is an extreme point of `M` if and only if
`q(θ) ∈ {0, 1}` for almost all `θ ∈ [θ̲, θ̄]`. -/
theorem extremePoint_monotoneAllocations_iff {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (g : L1Space θlo θhi) (hg : g ∈ monotoneAllocations θlo θhi) :
    IsExtremePoint (monotoneAllocations θlo θhi) g ↔
      ∀ᵐ x ∂(typeMeasure θlo θhi), (g : ℝ → ℝ) x = 0 ∨ (g : ℝ → ℝ) x = 1 := by sorry

end MechanismDesign.Screening
