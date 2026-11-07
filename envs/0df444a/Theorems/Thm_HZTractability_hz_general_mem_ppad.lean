-- Prove2me | Theorems.Thm_HZTractability_hz_general_mem_ppad
-- name    : HZTractability.hz_general_mem_ppad
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:10:53.13222+00:00
-- url     : https://prove2.me/theorems/b4dd66b8-1611-4ec9-9269-73dc7b2e4751
-- title:
--   [VY25, §7] membership (cited, p.1): normalized additive $\varepsilon$-equilibria are in PPAD
-- statement:
--   Cited by the paper from Vazirani and Yannakakis [VY25, Section 7]: the problem of finding a normalized additive $\varepsilon$-equilibrium (Definition 2.2) of an $N$-buyer HZ market with rational utilities in $[0,1]$, given $N\ge1$, the utilities and a positive rational accuracy $\varepsilon$, is in PPAD: it is total and reduces to End-of-Line by a polynomial-time search reduction.
--
--   The paper explains that [VY25]'s approximation notion imposes all conditions of Definition 2.2 together with an approximate minimum-expenditure condition, so dropping that condition gives a solution of this problem at the same error. This gives the membership half of Theorem 1.1, with accuracy $\varepsilon^*(a)/N$.
--
--   **Formalization Note** Not proved in this paper. The search problem is `HZGeneral`; PPAD is the public `QuasiStrictNE.PPAD`.
--
--   Differences from the source:
--   - reading: “Membership in PPAD follows from [VY25, Section 7]” (for [VY25]'s own notion, not defined in the paper) → the general problem `HZGeneral` (rational utilities in $[0,1]$, positive rational $\varepsilon$ in the input, answers Definition 2.2) is in PPAD; reason: this is the consequence the paper draws on p.1; every [VY25] answer is an answer here
--   - encoding: PPAD (not defined in the paper) → the public `QuasiStrictNE.PPAD`: total and Levin-reducible to End-of-Line; reason: standard definition
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §1.1, p.1 (PDF p.3), citing [VY25, Section 7]

import Mathlib
import Definitions.Def_QuasiStrictNE_PPAD
import Definitions.Def_HZTractability_HZGeneral

namespace HZTractability

/-- **[VY25, Section 7] membership, as quoted in** Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, §1.1, p.1 (PDF 3): "Membership in PPAD follows from
[VY25, Section 7]. Their approximation notion imposes all the conditions in Definition 2.2, together
with an approximate minimum-expenditure condition. Dropping that additional condition gives a
solution of our problem at the same error parameter. Their upper bound applies to rational utilities
in [0, 1] and positive rational accuracy, including ε∗(a)/N."

The search problem `HZGeneral` — given `N ≥ 1`, a rational `N × N` utility matrix with entries in
`[0, 1]` and a positive rational `ε`, find a rational normalized additive ε-equilibrium — is in PPAD
(total, and reducible to End-of-Line).

**Formalization Note** Cited from [VY25]; not proved in this paper. The paper does not define
[VY25]'s approximation notion; this is the consequence the paper draws from it. PPAD is the public
`QuasiStrictNE.PPAD`. -/
theorem hz_general_mem_ppad : HZGeneral ∈ QuasiStrictNE.PPAD := by sorry

end HZTractability
