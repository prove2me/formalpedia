-- Prove2me | Theorems.Thm_InteractiveConsistency_OralAlgorithm_procedure_assures_ic
-- name    : InteractiveConsistency.OralAlgorithm.procedure_assures_ic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:27.023976+00:00
-- url     : https://prove2.me/theorems/453707fe-d31d-4039-826a-51bc2a57d6a5
-- title:
--   Section 3 (pp. 230–231) — for n ≥ 3m + 1 the recursive procedure assures interactive consistency for m faults
-- statement:
--   Let $P$ be a finite set of $n$ processors and $m\ge 0$ with
--   $$n \ge 3m+1 .$$
--   Let every processor $p$ run the recursive procedure of Section 3 (steps (1)–(2), p. 230) on its own view $\sigma_p$, computing for each processor $r$ the value $\mathrm{record}(m, P, \sigma_p, r)\in V\cup\{\mathrm{NIL}\}$. Then this family assures interactive consistency for $m$ faults: for every set $N\subseteq P$ of nonfaulty processors with $|N|\ge n-m$ and every $(m+1)$-level scenario $\sigma$ consistent with $N$,
--
--   1. for all $p, q\in N$, $\mathrm{record}(m, P, \sigma_p, q) = \sigma(q)$ (each nonfaulty processor computes the private value of each nonfaulty processor);
--   2. for all $p, p'\in N$ and $r\in P$, $\mathrm{record}(m, P, \sigma_p, r) = \mathrm{record}(m, P, \sigma_{p'}, r)$ (all nonfaulty processors compute the same vector).
--
--   This is the positive half of the paper's characterization: interactive consistency is achievable with $m+1$ rounds of oral messages whenever $n\ge 3m+1$; the THEOREM of Section 4 shows that $n\ge 3m+1$ cannot be lowered.
--
--   **Formalization Note.** The paper proves this in prose ("The proof that the algorithm given above does indeed assure interactive consistency proceeds by induction on $m$"); the statement makes the claim explicit through `AssuresICLevel`. Each processor's procedure receives only its view `fun w => σ (p :: w)`, never $\sigma$ or $N$. The scenario is $(m+1)$-level: consistency with $N$ is assumed only on strings of length $\le m+2$, which is all the procedure reads. The case $m = 0$ (then $n\ge 1$) is included.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), pp. 230–231, Section 3 (procedure, p. 230; proof by induction on m, p. 231); interactive consistency: p. 229 (1)–(2), p. 232 (i)–(ii)

import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Procedure

namespace InteractiveConsistency.OralAlgorithm

theorem procedure_assures_ic {α V : Type*} [DecidableEq α] (P : Finset α) (m : ℕ)
    (hn : 3 * m + 1 ≤ P.card) :
    AssuresICLevel (V := V) P m (fun _ => record m P) := by sorry

end InteractiveConsistency.OralAlgorithm
