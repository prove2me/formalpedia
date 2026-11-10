-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_erasure_converse
-- name    : MultiPartyError1146.Adaptive.erasure_converse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:33:37.462423+00:00
-- url     : https://prove2.me/theorems/50b5bf60-73c9-4ec0-82ff-1faed7113486
-- title:
--   Theorem 5.1 — erasure converse at every rate
-- statement:
--   For all positive $n,m,T$, every deterministic adaptive $T$-round protocol and every erasure-resilience budget $\delta\in[0,1]$ satisfy
--   $$\delta\le6/\sqrt n.$$
--   The constant is absolute and independent of rate and duration. For $n\ge16$, the source attack with $k=\lceil\sqrt n\rceil$ has budget $2k/n+2/k\le6/\sqrt n$, and its outside receiver has local error at most $2/k$, within the factor-10 eligibility threshold. Smaller sizes follow from $\delta\le1$. Multibit inputs include the single differing-bit embedding.
--
--   Differences from the source:
--   - encoding: O(1/√n) erasure upper bound → the proof-supported absolute coefficient 6 for every positive n,m,T; reason: printed pp.31–32 give 2k/n+2/k; k=ceil(√n) for n≥16 and δ≤1 handle all sizes
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Theorem 5.1, printed p.30, PDF p.32

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Protocol

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem erasure_converse (n m T : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hT : 1 ≤ T)
    (P : Protocol n m T) (δ : ℝ) (hδ : Resilient P δ true) : δ ≤ 6 / Real.sqrt n := by sorry

end MultiPartyError1146.Adaptive
