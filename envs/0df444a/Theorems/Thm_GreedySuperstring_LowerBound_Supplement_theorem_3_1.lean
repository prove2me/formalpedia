-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_Supplement_theorem_3_1
-- name    : GreedySuperstring.LowerBound.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:38:50.255464+00:00
-- url     : https://prove2.me/theorems/446befb3-11d8-44fd-8283-0d1e8d81a9db
-- title:
--   Theorem 3.1 — the cycle-cover inequality $O\le\mathrm{OPT}+W$
-- statement:
--   Let $S$ be a finite substring-free set of nonempty words over any alphabet, and consider any complete run of the first stage of MGREEDY on $S$, with any tie-breaking. Let $O$ be the total overlap of the cycle-closing edges and $W$ the total prefix of the cycles of the resulting cycle cover, and let $\mathrm{OPT}$ be the length of a shortest common superstring of $S$. Then
--
--   $$O\le\mathrm{OPT}+W.$$
--
--   This is the cycle-cover inequality $O\le\mathrm{OPT}+\gamma W$ with $\gamma=1$, improving the earlier values $2$, $3/2$, $1.425$ and $1.396$. Combined with $W\le\mathrm{OPT}$ it shows that the greedy algorithm and MGREEDY are $3$-approximations, and, with a $2/3$-approximation for MAX-ATSP, gives a polynomial-time $7/3$-approximation for shortest common superstring. Theorem 3.3 shows that the coefficient $1$ of $W$ cannot be lowered.
--
--   Differences from the source:
--   - encoding: every instance of SCS, with the cycle cover 𝒞 constructed by MGREEDY → every finite substring-free set of nonempty words over any alphabet with decidable equality, and every complete run of the cycle-cover step relation; reason: the paper's standing assumptions (p.5) and its construction with arbitrary tie-breaking
--   - encoding: finite words over an arbitrary finite alphabet → lists over an arbitrary alphabet type with decidable equality (a linear order for Lyndon words); reason: each finite instance and its run uses finitely many symbols, so restriction to the occurring symbols recovers the source setting; length counts symbols
--   - encoding: the minimum common-superstring length OPT → the natural-number infimum of lengths of covering lists over the same alphabet; reason: concatenating the finite input always supplies a feasible word, so this infimum is an attained minimum, including zero for the empty input
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, Theorem 3.1, printed p.10 = PDF p.10; O and W defined §§2.3–2.4, pp.7–8

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_CycleCover

universe t31_u

namespace GreedySuperstring.LowerBound.Supplement

open GreedySuperstring.LowerBound

/-- Theorem 3.1, printed/PDF p.10. For every finite substring-free set `S` of nonempty words
over any alphabet and every complete run of MGREEDY's first stage on `S` (every
tie-breaking), `O ≤ OPT + W`. -/
theorem theorem_3_1 {α : Type t31_u} [DecidableEq α]
    (S : Finset (List α)) (hne : ∀ s ∈ S, s ≠ []) (hsf : SubstringFree S)
    (reps : List (Block α)) (hrun : IsCycleCoverRun S reps) :
    totalOverlap reps ≤ opt S + totalPrefix reps := by sorry

end GreedySuperstring.LowerBound.Supplement
