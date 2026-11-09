-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_fact_4_2
-- name    : MultiSpinCounting.Positive.fact_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:11.717804+00:00
-- url     : https://prove2.me/theorems/adf4f4b2-c01b-495c-be94-bfbefe045f9d
-- title:
--   Fact 4.2 — well-definedness, soundness and encoding length
-- statement:
--   For every positive rational instance $\Phi$ with $q\ge3$, active vertex $v$, depth $t\ge0$ and fixed $P\ge3$, the recursively constructed polytope is well-defined and contains the true marginal vector:
--   $$\mu_\Phi(v\leftarrow\cdot)\in\mathcal P_t(\Phi,v),\qquad \operatorname{bit}(\mathcal P_t(\Phi,v))\le Cq^3(|\Phi|+|V(\Phi)|P).$$
--   Here $C>0$ is absolute and precedes every instance, dimension, depth and precision. Well-definedness explicitly includes nonempty compact positive feasible sets, bounded attained Hilbert diameter, and, at positive depth, nonempty child optimization domains, positive denominators, and attained positive minima and attained maxima.
--
--   This supplies both the legitimate domains of the recursive optimization and the encoding-length bound of the actual rational constraint data.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and spin sets → Fin n and Fin q, with an active vertex subset; reason: relabeling preserves every instance; active subsets implement the source sub-instances and the fixed vertex order
--   - encoding: O(·) with an absolute implicit constant → one positive natural constant chosen before all inputs and dimensions; reason: the finitely many small encoding sizes are absorbed in this constant; no input is excluded
--   - encoding: the recursive construction is well-defined → domain, compactness, positivity and attainment are explicit conclusions; reason: these unpack well-defined extrema and the finite maximum used on p. 15, without adding hypotheses
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), pp. 14–15, Fact 4.2

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Polytopes

namespace MultiSpinCounting.Positive

/-- Fact 4.2, p. 14. Well-definedness includes the domains of the extrema, and the
positive compact domain on which a Hilbert diameter is an attained finite maximum. -/
theorem fact_4_2 :
    ∃ C : ℕ, 0 < C ∧ ∀ (n q : ℕ), 3 ≤ q → ∀ (Φ : Instance n q ℚ),
      IsPositive Φ → ∀ (P t : ℕ), 3 ≤ P → ∀ v : Fin n, v ∈ Φ.active →
      PolyWellDefined (polytope P t Φ v) ∧
      (match t with | 0 => True | s+1 => ExtremaWellDefined P s Φ v) ∧
      (fun a => marginal (realInstance Φ) v a) ∈ polytope P t Φ v ∧
      (encPoly (polyData P t Φ v)).length ≤
        C*q^3*((encInstance Φ).length + Φ.active.card*P) := by sorry

end MultiSpinCounting.Positive
