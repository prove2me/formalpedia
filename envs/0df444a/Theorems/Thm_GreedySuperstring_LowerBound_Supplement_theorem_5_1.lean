-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_Supplement_theorem_5_1
-- name    : GreedySuperstring.LowerBound.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:43:22.63098+00:00
-- url     : https://prove2.me/theorems/4353d1e2-6cd7-4adc-a0c5-24d57bfeb692
-- title:
--   Theorem 5.1 — strict $9/5$ bound for every greedy output on strings of length three
-- statement:
--   Let $S$ be a nonempty set of words of length three over any alphabet. Every output $g$ of the greedy algorithm on $S$, for every way of breaking ties, satisfies
--
--   $$|g|<\tfrac95\,\mathrm{OPT},$$
--
--   where $\mathrm{OPT}$ is the length of a shortest common superstring of $S$. Consequently $\rho_3\le9/5$, where $\rho_3$ is the supremum of $|g|/\mathrm{OPT}$ over all such inputs and outputs.
--
--   With Proposition 5.2 this determines $\rho_3=9/5$, settling the value between the bounds $5/3\le\rho_3\le2$ of Cazaux and Rivals and refuting their conjectured value $5/3$.
--
--   Differences from the source:
--   - encoding: |g| < 9/5 · OPT → 5·|g| < 9·OPT in ℕ; reason: the same strict inequality without division
--   - encoding: Consequently, ρ₃ ≤ 9/5 → no separate conjunct; reason: ρ₃ is the supremum of |g|/OPT over exactly the inputs and outputs quantified here, so it is the non-strict form of the stated universal bound
--   - encoding: finite words over an arbitrary finite alphabet → lists over an arbitrary alphabet type with decidable equality (a linear order for Lyndon words); reason: each finite instance and its run uses finitely many symbols, so restriction to the occurring symbols recovers the source setting; length counts symbols
--   - encoding: the minimum common-superstring length OPT → the natural-number infimum of lengths of covering lists over the same alphabet; reason: concatenating the finite input always supplies a feasible word, so this infimum is an attained minimum, including zero for the empty input
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, Theorem 5.1, printed p.23 = PDF p.23; ρ_k defined p.23

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_CycleCover

universe t51_u

namespace GreedySuperstring.LowerBound.Supplement

open GreedySuperstring.LowerBound

/-- Theorem 5.1, printed/PDF p.23. For every nonempty set `S` of words of length three over
any alphabet, every output `g` of the greedy algorithm on `S` (every tie-breaking) satisfies
`|g| < 9/5 · OPT`, written `5|g| < 9·OPT`. The non-strict consequence `ρ₃ ≤ 9/5` is the same
universal bound. -/
theorem theorem_5_1 {α : Type t51_u} [DecidableEq α]
    (S : Finset (List α)) (hS : S.Nonempty) (h3 : ∀ s ∈ S, s.length = 3)
    (g : List α) (hg : IsGreedyOutput S g) :
    5 * g.length < 9 * opt S := by sorry

end GreedySuperstring.LowerBound.Supplement
