-- Prove2me | Theorems.Thm_MinBuying_mtp2_summable_association
-- name    : MinBuying.mtp2_summable_association
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T18:05:27.783257+00:00
-- url     : https://prove2.me/theorems/1f23b70f-0e55-47f7-9102-9ff4af408675
-- title:
--   FKG association for summable MTP2 masses
-- statement:
--   Let $w$ be nonnegative and MTP2 on $\mathbb R^n$, and let $f,g$ be nonnegative increasing functions. If $w,wf,wg,wfg$ are summable, then $(\sum wf)(\sum wg)\le(\sum w)(\sum wfg)$. This is the countably supported association inequality without a finite-lattice or finite-support assumption.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript. https://doi.org/10.2139/ssrn.5178133 . Auxiliary affiliation and conditioning steps for the proof of Theorem 2, ec2–ec3. For association, the finite four-functions theorem is reused from Mathlib/Combinatorics/SetFamily/FourFunctions.lean.

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinBuying

theorem mtp2_summable_association (n : ℕ) (w f g : Valuations n → ℝ)
    (hw : ∀ v,0 ≤ w v) (hmtp : MTP2 w)
    (hf0 : ∀ v,0 ≤ f v) (hg0 : ∀ v,0 ≤ g v) (hf : Monotone f) (hg : Monotone g)
    (sw : Summable w) (sf : Summable (fun v => w v*f v))
    (sg : Summable (fun v => w v*g v))
    (sfg : Summable (fun v => w v*(f v*g v))) :
    (∑' v,w v*f v)*(∑' v,w v*g v) ≤
      (∑' v,w v)*(∑' v,w v*(f v*g v)) := by
  sorry

end MinBuying
