-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_optimal_error_resilience
-- name    : MultiPartyError1146.Adaptive.optimal_error_resilience
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:33:33.623759+00:00
-- url     : https://prove2.me/theorems/1a01bf9b-5fc2-4c30-8617-085ee19770d8
-- title:
--   Theorem 1.1 — optimal adaptive resilience and rate
-- statement:
--   The optimal deterministic adaptive CAS information-dissemination resilience has order $1/\sqrt n$, with the rate guarantee and erasure converse retained. For every $\eta>0$ there exist uniform $c_\eta,K_\eta>0$, $c_\eta\le1$, so that every positive $n,m$ admits a protocol with
--   $$\delta=c_\eta/\sqrt n,\qquad T\le K_\eta m n^{3/2+\eta}\log(2n).$$
--   There also exists one absolute $C>0$ such that for every positive $n,m,T$, every deterministic adaptive protocol and every erasure-resilience budget $\delta$,
--   $$\delta\le C/\sqrt n.$$
--   The correctness condition is full-vector recovery by every party within local error $10\delta$. The upper bound therefore also applies to corruption resilience. No supremum, fixed schedule, single-bit restriction or aggregate-only correctness condition replaces the operational theorem.
--
--   Differences from the source:
--   - encoding: Ωη(1/√n) resilience and tilde-Ωη(n^(−1/2−η)) rate → uniform cη,Kη>0 for all positive n,m, resilience cη/√n and duration at most Kη m n^(3/2+η) log(2n); reason: the proof has one logarithmic loss; log(2n) and uniform constant adjustment retain every small size
--   - encoding: informal maximum fraction Θ(1/√n) → conjunction of uniform operational achievability and erasure converse; reason: the precise versions are Theorems 4.1 and 5.1; avoiding a supremum changes no target
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Theorem 1.1, made precise by Theorems 4.1 and 5.1, printed p.2, PDF p.4

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Protocol

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem optimal_error_resilience : Achievability ∧ Converse := by sorry

end MultiPartyError1146.Adaptive
