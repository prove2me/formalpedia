-- Prove2me | Theorems.Thm_HorizontalPadicL_corollary_5_17_v2
-- name    : HorizontalPadicL.corollary_5_17_v2
-- status  : Open
-- author  : @davidloeffler
-- created : 2026-09-25T11:30:38.222227+00:00
-- url     : https://prove2.me/theorems/a9179663-c58b-474d-ac0a-aeed78a36eae
-- title:
--   Corollary 5.17 for new eigenforms
-- statement:
--   Let f be a new normalized eigenform of positive level and even weight at least two. If d is congruent to 2 modulo 4 and at least 6, then primitive characters of exact order d, conductor coprime to the level, and nonzero central critical twist have a positive logarithmic-power lower bound.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, pp. 41–42, Corollary 5.17 (with the conductor restricted to be coprime to the fixed level).

import Definitions.Def_KN_HorizontalPadicLAux

set_option autoImplicit false

namespace HorizontalPadicL

theorem corollary_5_17_v2
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (d : ℕ) (hcase1 : d % 4 = 2 ∧ 6 ≤ d) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound (eigenformNonvanishingCount ι f d) α := by sorry

end HorizontalPadicL
