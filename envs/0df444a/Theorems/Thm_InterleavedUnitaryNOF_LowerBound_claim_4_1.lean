-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_claim_4_1
-- name    : InterleavedUnitaryNOF.LowerBound.claim_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:08.242311+00:00
-- url     : https://prove2.me/theorems/383b8784-f59d-4700-ab91-7eb867a55c7e
-- title:
--   Claim 4.1 — identical NOF-view marginals
-- statement:
--   Let $m\ge1$, let $\nu$ be normalized Haar measure on $SU(m)$, and put $\mathcal X=\mathcal Y=SU(m)^4$ and $\mathcal Z=SU(m)^2$. Under $\mu_0$ all ten factors are independent Haar matrices. Under $\mu_1$ the first nine are independent and $E_2=(A_1B_1C_1D_1E_1A_2B_2C_2D_2)^{-1}$. For either law,
--
--   $$ (X,Y)\sim\nu^{\otimes4}\otimes\nu^{\otimes4},\quad (X,Z)\sim\nu^{\otimes4}\otimes\nu^{\otimes2},\quad (Y,Z)\sim\nu^{\otimes4}\otimes\nu^{\otimes2}. $$
--
--   Every player therefore has the same distribution of visible inputs under the two laws.
--
--   Differences from the source:
--   - encoding: positive matrix dimension and measurable Boolean functions on SU(m) powers → Fin m with NeZero m, normalized Borel Haar on the actual matrix group, and Bool indicators valued in ℝ; reason: these represent exactly the source objects, including m=1, without a discretization of the group
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Claim 4.1, printed p.10 = PDF p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem claim_4_1 : ∀ (m : ℕ) [NeZero m] (j : Bool),
    let μ := if j then mu1 m else mu0 m
    Measure.map (fun u : ContinuousInput m => (u.1,u.2.1)) μ =
      (haarPower m 4).prod (haarPower m 4) ∧
    Measure.map (fun u : ContinuousInput m => (u.1,u.2.2)) μ =
      (haarPower m 4).prod (haarPower m 2) ∧
    Measure.map (fun u : ContinuousInput m => (u.2.1,u.2.2)) μ =
      (haarPower m 4).prod (haarPower m 2) := by sorry

end InterleavedUnitaryNOF.LowerBound
