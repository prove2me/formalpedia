-- Prove2me | Theorems.Thm_MagicNumberShellModel_harmonic_oscillator_magic_numbers
-- name    : MagicNumberShellModel.harmonic_oscillator_magic_numbers
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T19:32:40.526397+00:00
-- url     : https://prove2.me/theorems/ab24b14a-9253-4cd5-a1ed-24947cd464c1
-- title:
--   Harmonic-oscillator derivation of the magic numbers
-- statement:
--   This is the complete content of the harmonic-oscillator derivation of the nuclear magic numbers. Let $L_n$ be the set of oscillator states at level $n$, let $C_n = 2\,|L_n|$ be the shell capacity including spin, let $S_N = \sum_{n<N} C_n$, and let $M = \{2, 8, 20, 28, 50, 82, 126\}$ be the seven most widely recognized magic numbers. Then all of the following hold.
--
--   1. **Closed form.** For every $N \ge 0$,
--   $$S_N \;=\; 2\binom{N+2}{3} \;=\; \frac{N(N+1)(N+2)}{3}.$$
--   2. **First predictions.** $(S_1, S_2, S_3, S_4) = (2, 8, 20, 40)$.
--   3. **Three genuine magic numbers.** $\{2, 8, 20\} \subseteq M$.
--   4. **A miss.** $28 \in M$, but $S_N \neq 28$ for every $N \ge 0$.
--   5. **A false prediction.** $S_4 = 40$, but $40 \notin M$.
--
--   Clauses 1–3 are the success of the model: degeneracy counting alone explains the magic numbers $2$, $8$ and $20$. Clauses 4–5 are its documented failure, and the reason the shell model requires spin–orbit coupling to reproduce the full list.
--
--   **Formalization Note.** All quantities are natural numbers and the binomial coefficients are the natural-number $\mathrm{choose}$ function, so no division appears. $M$ is a hard-coded finite set transcribing the source's list; clauses 3–5 are statements about that list, not about nuclear stability.
-- source:
--   Magic number (physics), Wikipedia, section "Derivation" (the 3D harmonic oscillator paragraph: weak 3-compositions counted by stars and bars, factor 2 for spin, cumulative sums 2, 8, 20, 40), and section lead (list of the seven magic numbers 2, 8, 20, 28, 50, 82, 126). https://en.wikipedia.org/wiki/Magic_number_(physics)

import Definitions.Def_magic_number_shell_model

namespace MagicNumberShellModel

theorem harmonic_oscillator_magic_numbers :
    (∀ N : ℕ, cumulativeCapacity N = 2 * (N + 2).choose 3) ∧
      List.map cumulativeCapacity [1, 2, 3, 4] = [2, 8, 20, 40] ∧
      ({2, 8, 20} : Finset ℕ) ⊆ magicNumbers ∧
      (28 ∈ magicNumbers ∧ ∀ N : ℕ, cumulativeCapacity N ≠ 28) ∧
      (cumulativeCapacity 4 = 40 ∧ 40 ∉ magicNumbers) := by sorry

end MagicNumberShellModel
