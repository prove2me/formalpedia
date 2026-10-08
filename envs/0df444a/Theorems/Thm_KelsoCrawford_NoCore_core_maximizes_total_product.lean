-- Prove2me | Theorems.Thm_KelsoCrawford_NoCore_core_maximizes_total_product
-- name    : KelsoCrawford.NoCore.core_maximizes_total_product
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:54.380496+00:00
-- url     : https://prove2.me/theorems/b8c72cf4-3377-4c7c-9bb4-1c3284b18465
-- title:
--   Section 6, p. 1503 — with transferable utility and σ = 0, every core allocation maximizes total product
-- statement:
--   Consider a job-matching market with finitely many workers and firms in which utility is transferable, $u^i(j; s) = s$ for every worker $i$, firm $j$ and salary $s$, and every reservation salary is zero, $\sigma_{ij} = 0$. Let $A$ be a core allocation (D3) of the market with continuously variable salaries, with assignment $f$. Then $f$ maximizes total product over all assignments of workers to firms: for every $g : W \to F$,
--   $$\sum_{j} y^j\big(g^{-1}(j)\big) \le \sum_{j} y^j\big(f^{-1}(j)\big).$$
--
--   In the example of Section 6 this is the first step of the proof that the core is empty: it restricts any core allocation to the assignments of maximal total product.
--
--   **Formalization Note** The paper states this inside the example ("because utility is transferable for both firms and workers, and because $\sigma_{ij} = \sigma_{ik} = 0$ for all workers, any core allocation must, by its Pareto efficiency, maximize total product over all feasible assignments"); it is stated here for every market with the two properties the sentence names. Assignments are total functions, so every worker is employed both in $A$ and in the competing assignment $g$, as in D1.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1503, Section 6

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Model
import Definitions.Def_KelsoCrawford_NoCore_Notions

namespace KelsoCrawford.NoCore

theorem core_maximizes_total_product {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (M : Market W F)
    (hu : ∀ i j s, M.u i j s = s) (hσ : ∀ i j, M.σ i j = 0)
    (A : Allocation W F) (hA : M.IsCore KelsoCrawford.ContinuousCore.anySalary A) (g : W → F) :
    M.totalProduct g ≤ M.totalProduct A.assign := by sorry

end KelsoCrawford.NoCore
