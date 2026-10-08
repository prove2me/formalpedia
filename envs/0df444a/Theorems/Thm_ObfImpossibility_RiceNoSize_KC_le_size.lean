-- Prove2me | Theorems.Thm_ObfImpossibility_RiceNoSize_KC_le_size
-- name    : ObfImpossibility.RiceNoSize.KC_le_size
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:44.435695+00:00
-- url     : https://prove2.me/theorems/e707c710-b4e0-4049-a29e-74f0b638649b
-- title:
--   Proof of Thm A.4, p. A:42 — $\mathrm{KC}([M])\le|M|$
-- statement:
--   For every machine $M$, the size of the smallest machine computing the same function as $M$ is at most the size of $M$:
--   $$\mathrm{KC}([M])\le |M|.$$
--
--   The proof of Theorem A.4 uses this inequality to show that the decider $T$, which only tries the inputs $x<|M|$, finds the input $x<\mathrm{KC}([M])$ witnessing $M\in\Pi_Y$.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:42, proof of Theorem A.4 ("x < KC([M]) ≤ |M|")

import Mathlib
import Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects

namespace ObfImpossibility.RiceNoSize

/-- p. A:42: `KC([M]) ≤ |M|` for every machine `M`. -/
theorem KC_le_size (M : Machine) : KC (fn M) ≤ size M := by sorry

end ObfImpossibility.RiceNoSize
