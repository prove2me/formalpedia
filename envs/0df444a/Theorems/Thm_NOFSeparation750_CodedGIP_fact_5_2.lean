-- Prove2me | Theorems.Thm_NOFSeparation750_CodedGIP_fact_5_2
-- name    : NOFSeparation750.CodedGIP.fact_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:43:33.813431+00:00
-- url     : https://prove2.me/theorems/32415a67-2fc6-4642-b257-eb1f275fce6c
-- title:
--   Fact 5.2 — accepting-cylinder cover from a nondeterministic protocol
-- statement:
--   For any product input space $X_1\times\cdots\times X_k$, any Boolean function $F$, and any correct operational nondeterministic NOF protocol $P$ with total cost at most $d$, there are $t\le2^d$ accepting cylinder intersections $A_1,\ldots,A_t$ such that
--   $$F^{-1}(1)=\bigcup_{a=1}^{t}A_a,\qquad A_a\subseteq F^{-1}(1).$$
--   The cost includes both the fixed-length certificate and worst-case verification communication over every input and certificate. The cover need not be disjoint. No cover property is assumed in protocol correctness; this theorem connects the operational model to the geometric one.
--
--   Differences from the source:
--   - encoding: a protocol of cost d → an operational protocol whose certificate length plus verification communication is at most d; reason: a bound is sufficient for the stated at-most-2^d conclusion and includes the exact-cost instance
--   - encoding: indices [r] and Boolean values {0,1} → zero-based Fin indices and Bool; reason: order-preserving relabeling changes no inputs, cylinders, or communication costs
-- source:
--   Haoyu Wang, Yimeng Wang, Pei Wu, STOC 2027 submission #750 (October 2026), Fact 5.2, p.8, citing [BDPW10, proof of Theorem 3.4]; operational model, p.6; canonical PDF SHA-256 b28ac89d573094bcafec49dc3a1eeadc9e95b5c3074c478d242f60a2818a42ce

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Cylinders

namespace NOFSeparation750.CodedGIP

/-- Fact 5.2, p.8: an implication from operational certificate protocols to covers,
not a definition of the protocol or its cost. -/
theorem fact_5_2 (k : ℕ) (X : Fin k → Type)
    (F : Input X → Bool) (P : NondetProtocol X) (d : ℕ)
    (hCorrect : P.Correct F) (hCost : P.Bounded d) :
    AcceptingCover F d := by sorry

end NOFSeparation750.CodedGIP
