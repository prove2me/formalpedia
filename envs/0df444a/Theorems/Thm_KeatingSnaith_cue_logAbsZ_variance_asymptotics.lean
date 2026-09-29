-- Prove2me | Theorems.Thm_KeatingSnaith_cue_logAbsZ_variance_asymptotics
-- name    : KeatingSnaith.cue_logAbsZ_variance_asymptotics
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T13:06:29.612063+00:00
-- url     : https://prove2.me/theorems/206d92ed-1eaa-4c06-a89d-cbaead448efb
-- title:
--   $Q_2 - \tfrac12\log N \to \tfrac12(\gamma+1)$
-- statement:
--   The **large-$N$ behaviour of the variance** of $\log|Z|$.
--
--   $$
--   \lim_{N\to\infty}\left(\bigl\langle (\log|Z|)^{2} \bigr\rangle_{\mathrm{CUE}(N)} - \tfrac12\log N\right) \;=\; \tfrac12(\gamma+1),
--   $$
--
--   where $\gamma$ denotes the Euler–Mascheroni constant. Equivalently, the variance is $\tfrac12\log N+\tfrac12(\gamma+1)+O(N^{-2})$, which is the content of eq. (2.2.18) of the source at the accuracy needed here.
--
--   This is the statement that justifies the normalisation used in the central limit theorem: the variance of $\log|Z|$ grows like $\tfrac12\log N$, so $\log|Z|/\sqrt{\tfrac12\log N}$ is the correctly standardised variable. The analogue for $\zeta$ is Selberg's theorem, where the variance is $\tfrac12\log\log T$.
-- source:
--   N. C. Snaith, Random Matrix Theory and zeta functions, PhD thesis, University of Bristol, June 2000, Chapter 2, p. 38, eq. (2.2.18): Q2 = (1/2) log N + (1/2)(gamma + 1) + 1/(24 N^2) - 1/(80 N^4) + O(N^-6)

import Definitions.Def_keating_snaith_cue

namespace KeatingSnaith

open Finset MeasureTheory Filter Topology
open scoped Real

/-- `Q₂ = ½ log N + ½(γ + 1) + O(N⁻²)` (thesis eq. (2.2.18)). -/
theorem cue_logAbsZ_variance_asymptotics :
    Tendsto (fun N : ℕ => cueAverage N (fun θ => logAbsZ N θ ^ 2) - Real.log N / 2)
      atTop (𝓝 ((Real.eulerMascheroniConstant + 1) / 2)) := by
  sorry

end KeatingSnaith
