-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_Supplement_lemma_5_6
-- name    : GreedySuperstring.LowerBound.Supplement.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:41:50.143663+00:00
-- url     : https://prove2.me/theorems/acb69d1b-3f91-4072-b816-f8e9935ea02a
-- title:
--   Lemma 5.6 — the overlap-one stage: $2\kappa_1\le\kappa_2+\pi(G_1)$
-- statement:
--   Let $S$ be a nonempty set of words of length three and consider any run of the greedy algorithm on $S$. Let $\kappa_2$ and $\kappa_1$ be the numbers of current strings after the overlap-two and the overlap-one stage, and let $G_1$ be the multigraph on symbols with one edge per current string after the overlap-two stage, from its first to its last symbol. Then
--
--   $$2\kappa_1\le\kappa_2+\pi(G_1).$$
--
--   The lemma bounds how many strings survive the overlap-one stage; combined with $\kappa_1\le\kappa_2$ and Lemma 5.7 it gives Theorem 5.1.
--
--   Differences from the source:
--   - encoding: κ₂ and κ₁ for a run of the greedy algorithm → |B₂| and |B₁| for any B₂ ending an overlap-two stage from S and any B₁ ending an overlap-one stage from B₂; reason: every run's two stage endpoints are such a pair; every such pair extends to a complete run by overlap-zero merges
--   - encoding: finite words over an arbitrary finite alphabet → lists over an arbitrary alphabet type with decidable equality (a linear order for Lyndon words); reason: each finite instance and its run uses finitely many symbols, so restriction to the occurring symbols recovers the source setting; length counts symbols
--   - encoding: the vertices of G₁ are the symbols appearing as endpoints of its edges → optional symbols as endpoints of the current words; reason: every current word is nonempty in this setting, so each endpoint is some symbol; None is never a vertex and adds no component
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, Lemma 5.6, printed p.26 = PDF p.26; stages p.23, G₁ p.26

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_CycleCover
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_LengthThree

universe l56_u

namespace GreedySuperstring.LowerBound.Supplement

open GreedySuperstring.LowerBound

/-- Lemma 5.6, printed/PDF p.26. For a nonempty set `S` of length-three words, a greedy run
on `S` whose overlap-two stage ends at `B₂` (`κ₂ = |B₂|`) and whose overlap-one stage ends at
`B₁` (`κ₁ = |B₁|`) satisfies `2κ₁ ≤ κ₂ + π(G₁)`. -/
theorem lemma_5_6 {α : Type l56_u} [DecidableEq α]
    (S : Finset (List α)) (hS : S.Nonempty) (h3 : ∀ s ∈ S, s.length = 3)
    (B2 B1 : Finset (Block α)) (hB2 : OverlapTwoStage S B2) (hB1 : OverlapOneStage B2 B1) :
    2 * B1.card ≤ B2.card + (G1 B2).trailCoverNumber := by sorry

end GreedySuperstring.LowerBound.Supplement
