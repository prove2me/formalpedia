-- Prove2me | Theorems.Thm_KeatingSnaith_cue_logAbsZ_mean
-- name    : KeatingSnaith.cue_logAbsZ_mean
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T12:59:14.254546+00:00
-- url     : https://prove2.me/theorems/951d4899-f1a8-41be-874b-5b4e6493a89b
-- title:
--   $\langle \log|Z|\rangle_{CUE} = 0$
-- statement:
--   The **first cumulant vanishes**: over $\mathrm{CUE}(N)$ the random variable $\log|Z|$ has mean zero, exactly and for every $N\ge1$.
--
--   $$
--   \bigl\langle \log|Z| \bigr\rangle_{\mathrm{CUE}(N)} \;=\; 0 .
--   $$
--
--   In the source this is obtained by differentiating the moment generating function $M_N(s)$ at $s=0$, using $\psi(j+s)-\psi(j+s/2)\big|_{s=0}=0$. It is the reason no centring appears in the central limit theorem of this mission: $\log|Z|$ is already centred at every matrix size, and one only has to divide by $\sqrt{\tfrac12\log N}$.
-- source:
--   N. C. Snaith, Random Matrix Theory and zeta functions, PhD thesis, University of Bristol, June 2000, Chapter 2, p. 36, eq. (2.2.6)

import Definitions.Def_keating_snaith_cue

namespace KeatingSnaith

open Finset MeasureTheory Filter Topology
open scoped Real

/-- `⟨log |Z|⟩ = 0` (thesis eq. (2.2.6)). -/
theorem cue_logAbsZ_mean (N : ℕ) (hN : 1 ≤ N) :
    cueAverage N (fun θ => logAbsZ N θ) = 0 := by
  sorry

end KeatingSnaith
