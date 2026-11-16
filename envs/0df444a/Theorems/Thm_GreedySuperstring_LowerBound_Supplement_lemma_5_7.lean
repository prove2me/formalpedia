-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_Supplement_lemma_5_7
-- name    : GreedySuperstring.LowerBound.Supplement.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:42:35.38858+00:00
-- url     : https://prove2.me/theorems/99c20590-b7d4-4c7f-b0b9-d14f7d26c98f
-- title:
--   Lemma 5.7 — main lemma: $\pi(G_1)\le4\nu+\sum_{P\in\mathcal T}\mathrm{contr}(P)$
-- statement:
--   Let $S$ be a nonempty set of words of length three and consider any run of the greedy algorithm on $S$, with overlap-two trail cover $\mathcal T$ of $G_2$. With $\nu$, $G_1$ and $\mathrm{contr}$ as in §5.1,
--
--   $$\pi(G_1)\le4\nu+\sum_{P\in\mathcal T}\mathrm{contr}(P).$$
--
--   Here $\mathrm{contr}(P)=2m_P-4$ for a closed trail and $2m_P$ for an open trail with $m_P$ edges, so loops contribute $-2$. This is the main lemma of §5; by the computation on p.27 it is equivalent to inequality (6), from which Theorem 5.1 follows.
--
--   Differences from the source:
--   - encoding: T formed by the overlap-two stage of the run → the histories of the blocks of any state B₂ ending an overlap-two stage from S; reason: as in Lemma 5.4
--   - encoding: an inequality between integers with contr possibly negative → an inequality in ℤ; reason: contr(P) = −2 for a one-edge closed trail
--   - encoding: finite words over an arbitrary finite alphabet → lists over an arbitrary alphabet type with decidable equality (a linear order for Lyndon words); reason: each finite instance and its run uses finitely many symbols, so restriction to the occurring symbols recovers the source setting; length counts symbols
--   - encoding: the vertices of G₁ are the symbols appearing as endpoints of its edges → optional symbols as endpoints of the current words; reason: every current word is nonempty in this setting, so each endpoint is some symbol; None is never a vertex and adds no component
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, Lemma 5.7, printed p.27 = PDF p.27; contr defined p.27

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_CycleCover
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_LengthThree

universe l57_u

namespace GreedySuperstring.LowerBound.Supplement

open GreedySuperstring.LowerBound

/-- Lemma 5.7, printed/PDF p.27 (main lemma). For a nonempty set `S` of length-three words
and the state `B₂` after the overlap-two stage of any greedy run on `S`,
`π(G₁) ≤ 4ν + Σ_{P ∈ T} contr(P)` in `ℤ`. -/
theorem lemma_5_7 {α : Type l57_u} [DecidableEq α]
    (S : Finset (List α)) (hS : S.Nonempty) (h3 : ∀ s ∈ S, s.length = 3)
    (B2 : Finset (Block α)) (hB2 : OverlapTwoStage S B2) :
    ((G1 B2).trailCoverNumber : ℤ) ≤ 4 * (nu S B2 : ℤ) + ∑ b ∈ B2, contr b.history := by sorry

end GreedySuperstring.LowerBound.Supplement
