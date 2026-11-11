-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_claim_4_5
-- name    : InterleavedUnitaryNOF.LowerBound.claim_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:55.154148+00:00
-- url     : https://prove2.me/theorems/a625a369-5095-4046-825b-8305d6d76b39
-- title:
--   Claim 4.5 — finite-type approximation for both measures
-- statement:
--   Let $m\ge1$ and let $c$ be any measurable Boolean cylinder indicator on $\mathcal X\times\mathcal Y\times\mathcal Z$, where $\mathcal X=\mathcal Y=SU(m)^4$ and $\mathcal Z=SU(m)^2$. For every integer $r\ge1$, there is a cylinder $c_r$ whose factors are constant on finite equal-Haar-measure partitions, with
--
--   $$|\mu_j(c)-\mu_j(c_r)|\le1/r\qquad(j=0,1).$$
--
--   The same approximation works for both the independent and constrained laws.
--
--   Differences from the source:
--   - encoding: positive matrix dimension and measurable Boolean functions on SU(m) powers → Fin m with NeZero m, normalized Borel Haar on the actual matrix group, and Bool indicators valued in ℝ; reason: these represent exactly the source objects, including m=1, without a discretization of the group
--   - encoding: the expectation of c−c_r → the difference of the two expectations; reason: both measurable Boolean indicators are integrable under the explicitly normalized probability laws
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Claim 4.5, printed p.12 = PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem claim_4_5 (m : ℕ) [NeZero m] (c : Cylinder m) (r : ℕ) (hr : 1 ≤ r) :
    ∃ cr : Cylinder m, FiniteType cr ∧ ∀ j : Bool,
      |mass (if j then mu1 m else mu0 m) c -
        mass (if j then mu1 m else mu0 m) cr| ≤ 1/(r : ℝ) := by sorry

end InterleavedUnitaryNOF.LowerBound
