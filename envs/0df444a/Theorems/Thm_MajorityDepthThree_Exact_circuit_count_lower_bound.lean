-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_circuit_count_lower_bound
-- name    : MajorityDepthThree.Exact.circuit_count_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:25.405548+00:00
-- url     : https://prove2.me/theorems/1dc878e2-50bd-4123-afff-891213fca44b
-- title:
--   Fact 2.9 — top fan-in bound and attained positive extremal count
-- statement:
--   Let $n,k\ge1$ and $0\le t\le n$. The extremal count $\Theta(n,t,k)$ over all valid signed $t$-threshold width-at-most-$k$ CNFs is positive and attained. Every such depth-three circuit $C$ computing the $t$-threshold function on every input satisfies
--
--   $$|C|\ge\frac{\binom nt}{\Theta(n,t,k)}.$$
--
--   Here $|C|$ is the number of CNFs under the top OR gate. Positivity and attainment are explicit conclusions rather than assumptions or a substituted value for the maximum. This is the source's circuit lower bound from boundary-layer counting.
--
--   Differences from the source:
--   - encoding: n Boolean variables → The fixed carrier Fin n with ambient set univ; reason: Relabeling preserves clauses, assignments, weights and top fan-in; the theorem retains its stated parameter domain
--   - encoding: The maximum Θ used as a denominator → A computed finite maximum, with positivity and an extremal formula explicitly asserted; reason: Finite syntax gives attainment, and t positive units give a nonzero t-layer count; these are the well-posedness facts implicit in the notation
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.7, Fact 2.9 and Definition 2.6

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false

namespace MajorityDepthThree.Exact

theorem circuit_count_lower_bound (n t k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (ht : t ≤ n) :
    (0 < thetaMax (Finset.univ : Finset (Fin n)) t k) ∧
    (∃ F : CNF (Fin n), Extremal Finset.univ F t k) ∧
    (∀ C : Circuit (Fin n), CircuitValid Finset.univ k C → ComputesThreshold Finset.univ t C →
      (Nat.choose n t : ℝ) / (thetaMax (Finset.univ : Finset (Fin n)) t k : ℝ) ≤ (C.length : ℝ)) := by sorry

end MajorityDepthThree.Exact
