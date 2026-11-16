-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_Supplement_lemma_2_4
-- name    : GreedySuperstring.LowerBound.Supplement.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:38:01.529182+00:00
-- url     : https://prove2.me/theorems/28f19546-89fc-428e-b5c0-f0ba0f41d425
-- title:
--   Lemma 2.4 — cyclic substrings of each cycle string occur in every shortest superstring
-- statement:
--   Fix a linear order on the alphabet. Let $S$ be a finite substring-free set of nonempty words and consider any complete run of the first stage of MGREEDY on $S$. For every cycle $C$ of the resulting cycle cover, with cycle-closing overlap $o(C)$, cycle string $\tau(C)$ and Lyndon conjugate $\tau'(C)$, and for every shortest common superstring $\mathrm{OPT}$ of $S$,
--
--   $$\mathrm{CSub}_{o(C)+1}(\tau'(C))=\mathrm{CSub}_{o(C)+1}(\tau(C))\subseteq\mathrm{Sub}_{o(C)+1}(\mathrm{OPT}).$$
--
--   The lemma is stated in the paper with a citation to Blum, Jiang, Li, Tromp and Yannakakis (1994, Claim 2). It ties each cycle of the greedy cycle cover to the substrings of an optimal solution, which is the input to the counting Lemma 3.2 in the proof of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: τ′(C), the unique Lyndon word equivalent to τ(C) → the lexicographically least cyclic rotation of τ(C); reason: τ(C) is primitive (Lemma 2.3), so its least rotation is that Lyndon word; no Lyndon property is assumed
--   - encoding: OPT, an optimal common superstring of S → every word that contains every member of S and has length OPT(S); reason: the paper fixes an arbitrary optimal superstring; the statement is required for each one
--   - encoding: finite words over an arbitrary finite alphabet → lists over an arbitrary alphabet type with decidable equality (a linear order for Lyndon words); reason: each finite instance and its run uses finitely many symbols, so restriction to the occurring symbols recovers the source setting; length counts symbols
--   - encoding: the minimum common-superstring length OPT → the natural-number infimum of lengths of covering lists over the same alphabet; reason: concatenating the finite input always supplies a feasible word, so this infimum is an attained minimum, including zero for the empty input
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, Lemma 2.4, printed p.10 = PDF p.10; definitions of Sub, CSub, τ′ p.10; Lyndon words p.9

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_WordCombinatorics
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_CycleCover

universe l24_u

namespace GreedySuperstring.LowerBound.Supplement

open GreedySuperstring.LowerBound

/-- Lemma 2.4, printed/PDF p.10 (cited from [BJL+94, Claim 2]). Fix a linear order on the
alphabet. For every complete run of MGREEDY's first stage on a substring-free set of nonempty
words, every extracted cycle `C` and every shortest common superstring `OPT` of `S`,
`CSub_{o(C)+1}(τ′(C)) = CSub_{o(C)+1}(τ(C)) ⊆ Sub_{o(C)+1}(OPT)`, where `τ′(C)` is the
least cyclic rotation of `τ(C)`. -/
theorem lemma_2_4 {α : Type l24_u} [LinearOrder α]
    (S : Finset (List α)) (hne : ∀ s ∈ S, s ≠ []) (hsf : SubstringFree S)
    (reps : List (Block α)) (hrun : IsCycleCoverRun S reps) :
    ∀ C ∈ reps, ∀ OPTword : List α, IsShortestSuperstring S OPTword →
      cyclicSubwords (cycleOverlap C.history + 1) (leastRotation (cycleString C.history)) =
          cyclicSubwords (cycleOverlap C.history + 1) (cycleString C.history) ∧
        cyclicSubwords (cycleOverlap C.history + 1) (cycleString C.history) ⊆
          subwords (cycleOverlap C.history + 1) OPTword := by sorry

end GreedySuperstring.LowerBound.Supplement
