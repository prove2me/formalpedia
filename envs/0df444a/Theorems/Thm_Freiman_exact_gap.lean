-- Prove2me | Theorems.Thm_Freiman_exact_gap
-- name    : Freiman.exact_gap
-- status  : Proved
-- author  : @tp
-- created : 2026-09-08T23:23:53.979098+00:00
-- url     : https://prove2.me/theorems/5a05e1fd-6961-40df-9cc7-e592d389b76a
-- title:
--   The exact Markov gap below Freiman's constant
-- statement:
--   Let $\mu_*$ and $c_F$ be the exact constants defined above. Both endpoints belong to the classical Markov spectrum, and there is no Markov value strictly between them:
--   $$
--   \mu_*\in M,\qquad c_F\in M,\qquad
--   M\cap(\mu_*,c_F)=\varnothing.
--   $$
--   Together with $\mu_*<c_0<c_F$, this supplies the gap below $c_F$ used to establish maximality of the Hall ray.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Theorem 20.6, p. 71; the exact expression for the lower endpoint is equation (20.1), p. 65. The construction occupies Part V.

import Definitions.Def_Freiman_cF
import Definitions.Def_Freiman_gapThreshold
import Definitions.Def_Freiman_markovSpectrum

namespace Freiman

theorem exact_gap :
    gapLeft ∈ markovSpectrum ∧ cF ∈ markovSpectrum ∧
    (markovSpectrum ∩ Set.Ioo gapLeft cF) = ∅ := by
  sorry

end Freiman
