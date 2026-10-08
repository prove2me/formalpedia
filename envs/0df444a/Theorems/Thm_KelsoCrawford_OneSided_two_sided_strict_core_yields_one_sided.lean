-- Prove2me | Theorems.Thm_KelsoCrawford_OneSided_two_sided_strict_core_yields_one_sided
-- name    : KelsoCrawford.OneSided.two_sided_strict_core_yields_one_sided
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:54.322993+00:00
-- url     : https://prove2.me/theorems/88e90feb-132f-46f4-ada8-3e3f332af497
-- title:
--   Section 4 — a fictitious-market strict core yields a one-sided strict core
-- statement:
--   Let $v$ satisfy nonnegative marginal production (MP′) and no free lunch (NFL), and let each worker's salary utility $\mu^i$ be strictly increasing and continuous. Suppose $A$ is a strict-core allocation of the fictitious market with $m+1$ identical firms. Partition the workers by their employer in $A$ and retain their salaries. The resulting one-sided allocation $(P,s)$ satisfies D1′ and D2′:
--
--   $$ (P,s)\in\operatorname{StrictCore}_{\mathrm{one\text{-}sided}}(v). $$
--
--   This transfer is the final implication in the paper's proof of Theorem 3.
--
--   **Formalization Note** The partition omits firms hiring no workers. It uses the paper's single aggregate budget inequality and rules out exactly the improving coalitions with a strict salary gain for some worker.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1493–1494, Section 4, proof of Theorem 3, final sentence

import Mathlib
import Definitions.Def_KelsoCrawford_OneSided_Model
import Definitions.Def_KelsoCrawford_OneSided_OneSided
import Definitions.Def_KelsoCrawford_OneSided_Fictitious

namespace KelsoCrawford.OneSided

theorem two_sided_strict_core_yields_one_sided {W : Type} [Fintype W] [DecidableEq W]
    (v : Finset W → ℝ) (μ : W → ℝ → ℝ)
    (hMP : ∀ i (C : Finset W), 0 ≤ v (insert i C) - v C)
    (hNFL : v ∅ = 0)
    (hμ : ∀ i, StrictMono (μ i) ∧ Continuous (μ i))
    (A : Allocation W (Fin (Fintype.card W + 1)))
    (hcore : (fictitious v μ).IsStrictCore KelsoCrawford.ContinuousCore.anySalary A) :
    IsOneSidedStrictCore v (employerPartition A) A.sal := by sorry

end KelsoCrawford.OneSided
