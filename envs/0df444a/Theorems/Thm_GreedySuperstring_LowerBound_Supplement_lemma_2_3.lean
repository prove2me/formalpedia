-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_Supplement_lemma_2_3
-- name    : GreedySuperstring.LowerBound.Supplement.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:37:19.241446+00:00
-- url     : https://prove2.me/theorems/9349a2e1-a1fe-4557-8aad-54a114f92169
-- title:
--   Lemma 2.3 — MGREEDY cycle strings are primitive and pairwise non-equivalent
-- statement:
--   Let $S$ be a finite substring-free set of nonempty words over an alphabet, and consider any complete run of the first stage of MGREEDY on $S$, with any tie-breaking. Let $\mathcal C$ be the resulting cycle cover, one cycle per extracted representative. Then:
--
--   1. for every $C\in\mathcal C$ the cycle string $\tau(C)$ is primitive, that is, $\tau(C)\ne v^k$ for every word $v$ and every $k\ge2$;
--   2. for any two distinct cycles $C\ne D$ of $\mathcal C$, the cycle strings $\tau(C)$ and $\tau(D)$ are not cyclic rotations of each other.
--
--   The lemma is stated in the paper with a citation to Mucha (2013). It is the source of the distinctness of the Lyndon words $\tau'(C)$ in the proof of the cycle-cover inequality, Theorem 3.1.
--
--   Differences from the source:
--   - encoding: the cycle cover 𝒞 constructed by MGREEDY → the list of blocks extracted by an arbitrary complete run of the cycle-cover step relation; reason: the paper's construction with arbitrary tie-breaking is exactly this run; each extracted history (t₁,…,t_r) is the cycle (t₁,…,t_r,t₁)
--   - encoding: distinct cycles of 𝒞 → distinct positions of the representative list; reason: distinct extracted blocks are distinct cycles; positions also separate any equal entries
--   - encoding: equivalent (one is a cyclic rotation of the other) → Mathlib's List.IsRotated; reason: same relation
--   - encoding: finite words over an arbitrary finite alphabet → lists over an arbitrary alphabet type with decidable equality (a linear order for Lyndon words); reason: each finite instance and its run uses finitely many symbols, so restriction to the occurring symbols recovers the source setting; length counts symbols
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, Lemma 2.3, printed p.9 = PDF p.9; standing assumptions p.5; MGREEDY §2.4 p.8

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_WordCombinatorics
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_CycleCover

universe l23_u

namespace GreedySuperstring.LowerBound.Supplement

open GreedySuperstring.LowerBound

/-- Lemma 2.3, printed/PDF p.9 (cited from [Muc13, Lemma 2.5]). For every complete run of
MGREEDY's first stage on a substring-free set of nonempty words (every tie-breaking), every
cycle string `τ(C)` is primitive, and the cycle strings of two distinct extracted cycles
(distinct positions in the representative list) are not cyclic rotations of each other. -/
theorem lemma_2_3 {α : Type l23_u} [DecidableEq α]
    (S : Finset (List α)) (hne : ∀ s ∈ S, s ≠ []) (hsf : SubstringFree S)
    (reps : List (Block α)) (hrun : IsCycleCoverRun S reps) :
    (∀ C ∈ reps, IsPrimitive (cycleString C.history)) ∧
    ∀ i j : Fin reps.length, i ≠ j →
      ¬ Equivalent (cycleString (reps.get i).history) (cycleString (reps.get j).history) := by sorry

end GreedySuperstring.LowerBound.Supplement
