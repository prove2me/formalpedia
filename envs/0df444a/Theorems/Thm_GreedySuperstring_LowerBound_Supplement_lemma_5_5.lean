-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_Supplement_lemma_5_5
-- name    : GreedySuperstring.LowerBound.Supplement.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:41:11.468217+00:00
-- url     : https://prove2.me/theorems/3b9835f8-3efe-4565-80a5-097c290355c8
-- title:
--   Lemma 5.5 — $\mathrm{OPT}\ge n+\pi(G_2)+1$ for strings of length three
-- statement:
--   Let $S$ be a nonempty set of $n$ words of length three. Then the length of a shortest common superstring of $S$ satisfies
--
--   $$\mathrm{OPT}\ge n+\pi(G_2)+1,$$
--
--   where $\pi(G_2)$ is the minimum number of trails covering the edges of the graph $G_2$ of $S$.
--
--   This is the lower bound on the optimum against which the greedy output is compared in Theorem 5.1.
--
--   Differences from the source:
--   - encoding: finite words over an arbitrary finite alphabet → lists over an arbitrary alphabet type with decidable equality (a linear order for Lyndon words); reason: each finite instance and its run uses finitely many symbols, so restriction to the occurring symbols recovers the source setting; length counts symbols
--   - encoding: the minimum common-superstring length OPT → the natural-number infimum of lengths of covering lists over the same alphabet; reason: concatenating the finite input always supplies a feasible word, so this infimum is an attained minimum, including zero for the empty input
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, Lemma 5.5, printed p.26 = PDF p.26; G₂ defined p.23

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_CycleCover
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_LengthThree

universe l55_u

namespace GreedySuperstring.LowerBound.Supplement

/-- Lemma 5.5, printed/PDF p.26. For every nonempty set `S` of `n` words of length three,
`OPT ≥ n + π(G₂) + 1`. -/
theorem lemma_5_5 {α : Type l55_u} [DecidableEq α]
    (S : Finset (List α)) (hS : S.Nonempty) (h3 : ∀ s ∈ S, s.length = 3) :
    S.card + (G2 S).trailCoverNumber + 1 ≤ opt S := by sorry

end GreedySuperstring.LowerBound.Supplement
