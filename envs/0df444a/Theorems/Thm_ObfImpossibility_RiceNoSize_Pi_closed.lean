-- Prove2me | Theorems.Thm_ObfImpossibility_RiceNoSize_Pi_closed
-- name    : ObfImpossibility.RiceNoSize.Pi_closed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:57.88564+00:00
-- url     : https://prove2.me/theorems/43d79541-93c1-4af9-b0cb-b1ae6c7ebfcf
-- title:
--   Proof of Thm A.4, p. A:42 — $\Pi$ is closed under $[\cdot]$
-- statement:
--   Let $\Pi=(\Pi_Y,\Pi_N)$ be the promise problem of the proof of Theorem A.4:
--   $\Pi_Y$ consists of the machines that always halt and output $1$ on some input $x<\mathrm{KC}([M])$, and $\Pi_N$ of the machines that always halt and output $0$ on every input. Then $\Pi$ is closed under $[\cdot]$: for all machines $M,M'$,
--   $$[M]=[M'] \;\Longrightarrow\; \big(M\in\Pi_Y\iff M'\in\Pi_Y\big)\ \text{and}\ \big(M\in\Pi_N\iff M'\in\Pi_N\big).$$
--
--   This is the first of the two properties that make $\Pi$ an instance of the hypothesis of Conjecture A.3.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:42, proof of Theorem A.4 ("It is obvious that Π is closed under [·].")

import Mathlib
import Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects

namespace ObfImpossibility.RiceNoSize

/-- p. A:42: the promise problem `Π = (Π_Y, Π_N)` of the proof of Theorem A.4 is closed
under `[·]`. -/
theorem Pi_closed : ClosedUnderFn PiY PiN := by sorry

end ObfImpossibility.RiceNoSize
