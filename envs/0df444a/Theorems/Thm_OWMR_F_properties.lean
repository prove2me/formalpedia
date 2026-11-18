-- Prove2me | Theorems.Thm_OWMR_F_properties
-- name    : OWMR.F_properties
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T02:42:37.55659+00:00
-- url     : https://prove2.me/theorems/d5d2468c-55b8-4f23-9673-bc5752defde0
-- title:
--   Regularity of the retailer cost $F_i$
-- statement:
--   Consider an OWMR network that satisfies the standing assumptions and a retailer $i$, with lead-time demand $Z_i$ a sum of $L_i+1$ i.i.d. demands of retailer $i$, and
--
--   $$F_i(y)=\mathbb E\bigl[H_i(y-Z_i)^++p(Z_i-y)^+\bigr].$$
--
--   Then $F_i\ge0$; $F_i$ is convex on $\mathbb R$; $|F_i(y)-F_i(y')|\le(H_i+p)|y-y'|$ for all $y,y'$; and $F_i$ has slopes at least $-p$: $F_i(y)-p(y'-y)\le F_i(y')$ whenever $y\le y'$.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), eq. (8) and its footnote, p. 12 ("F_i finite and globally Lipschitz"); convexity and the slope bound F(S-x) >= G - p(w-x) are used in Step 1 of the proof of Lemma 3, p. 14.

import Definitions.Def_owmr_single_location

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem F_properties {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) :
    (∀ y, 0 ≤ N.F i y) ∧ ConvexOn ℝ Set.univ (N.F i) ∧
      (∀ y y', |N.F i y - N.F i y'| ≤ (N.H i + N.p) * |y - y'|) ∧
      (∀ y y', y ≤ y' → N.F i y - N.p * (y' - y) ≤ N.F i y') := by sorry
end OWMR
