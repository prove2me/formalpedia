-- Prove2me | Theorems.Thm_MagicNumberShellModel_misses_28_and_predicts_40
-- name    : MagicNumberShellModel.misses_28_and_predicts_40
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T18:49:28.606974+00:00
-- url     : https://prove2.me/theorems/e1193f05-1543-4fc8-94a6-41d2ba977344
-- title:
--   The oscillator count misses $28$ and predicts the non-magic $40$
-- statement:
--   Let $M = \{2, 8, 20, 28, 50, 82, 126\}$ be the seven most widely recognized magic numbers and let $S_N$ be the harmonic-oscillator shell-filling count. Then both failures of the oscillator model recorded by the source hold:
--
--   1. $28 \in M$, yet $S_N \neq 28$ for **every** $N \ge 0$: the magic number $28$ is never a shell closure of the pure oscillator.
--   2. $S_4 = 40$, yet $40 \notin M$: the model predicts a closure at $40$ nucleons, which is not a magic number.
--
--   These are the two discrepancies that spin–orbit coupling was introduced to repair. The first claim quantifies over all $N$, so it is not a finite check: it needs the closed form for $S_N$ together with its monotonicity in $N$.
-- source:
--   Magic number (physics), Wikipedia, section "Derivation" (the 3D harmonic oscillator paragraph: weak 3-compositions counted by stars and bars, factor 2 for spin, cumulative sums 2, 8, 20, 40), and section lead (list of the seven magic numbers 2, 8, 20, 28, 50, 82, 126). https://en.wikipedia.org/wiki/Magic_number_(physics)

import Definitions.Def_magic_number_shell_model

namespace MagicNumberShellModel

theorem misses_28_and_predicts_40 :
    (28 ∈ magicNumbers ∧ ∀ N : ℕ, cumulativeCapacity N ≠ 28) ∧
      cumulativeCapacity 4 = 40 ∧ 40 ∉ magicNumbers := by sorry

end MagicNumberShellModel
