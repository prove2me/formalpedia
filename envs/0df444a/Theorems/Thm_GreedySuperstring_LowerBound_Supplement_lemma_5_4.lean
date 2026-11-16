-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_Supplement_lemma_5_4
-- name    : GreedySuperstring.LowerBound.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:40:29.391312+00:00
-- url     : https://prove2.me/theorems/6109e4f4-1f2e-4737-a3f4-94e393f36352
-- title:
--   Lemma 5.4 — the overlap-two stage leaves exactly $\pi(G_2)-\nu$ open trails
-- statement:
--   Let $S$ be a nonempty set of words of length three and consider any run of the greedy algorithm on $S$. Let $\mathcal T$ be the trail cover of $G_2$ formed by the overlap-two stage, one trail per current string after that stage, and let $\nu$ be the number of weak components of $G_2$ containing no open trail of $\mathcal T$. Then $\mathcal T$ has exactly
--
--   $$\pi(G_2)-\nu$$
--
--   open trails.
--
--   The lemma shows that the overlap-two stage of greedy produces the minimum possible number of open trails; it enters the definition of $\mathrm{contr}(P)$ and the reduction of Theorem 5.1 to Lemma 5.7.
--
--   Differences from the source:
--   - encoding: T, the trail cover formed by the overlap-two stage of the run → the histories of the blocks of any state B₂ reachable by greedy steps of overlap 2 at which no two distinct current words overlap by 2 or more; reason: every run's state after its overlap-two stage is such a B₂, and every such B₂ arises so
--   - encoding: T has exactly π(G₂) − ν open trails → #open trails + ν = π(G₂) in ℕ; reason: the same equality without truncated subtraction
--   - encoding: finite words over an arbitrary finite alphabet → lists over an arbitrary alphabet type with decidable equality (a linear order for Lyndon words); reason: each finite instance and its run uses finitely many symbols, so restriction to the occurring symbols recovers the source setting; length counts symbols
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, Lemma 5.4, printed p.25 = PDF p.25; setting §5 p.23 and §5.1 p.25

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_CycleCover
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_LengthThree

universe l54_u

namespace GreedySuperstring.LowerBound.Supplement

open GreedySuperstring.LowerBound

/-- Lemma 5.4, printed/PDF p.25. For a nonempty set `S` of length-three words and the state
`B₂` after the overlap-two stage of any greedy run on `S`, the trail cover `T` (histories of
the blocks of `B₂`) has exactly `π(G₂) − ν` open trails, written as an equality in `ℕ`. -/
theorem lemma_5_4 {α : Type l54_u} [DecidableEq α]
    (S : Finset (List α)) (hS : S.Nonempty) (h3 : ∀ s ∈ S, s.length = 3)
    (B2 : Finset (Block α)) (hB2 : OverlapTwoStage S B2) :
    (openTrails B2).card + nu S B2 = (G2 S).trailCoverNumber := by sorry

end GreedySuperstring.LowerBound.Supplement
