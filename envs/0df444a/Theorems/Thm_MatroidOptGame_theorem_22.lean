-- Prove2me | Theorems.Thm_MatroidOptGame_theorem_22
-- name    : MatroidOptGame.theorem_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:24.307132+00:00
-- url     : https://prove2.me/theorems/e7954d75-c591-4191-8e30-5780ecc6892b
-- title:
--   Theorem 22 — matroid red-blue rules
-- statement:
--   Let $M$ be a finite matroid with weights $w : E \to \mathbb N$ and let $B$ be a base of $M$. The following are equivalent:
--   1. $B$ is a minimum-weight base of $M$ with respect to $w$.
--   2. For every $e \in B$, every cut (cocircuit) $C$ of $M$ with $C \cap B = \{e\}$, and every $f \in C$: $w(e) \le w(f)$.
--   3. For every circuit $C$ of $M$ with $|C \setminus B| = 1$, writing $C \setminus B = \{f\}$, every $e \in C$ satisfies $w(e) \le w(f)$.
--
--   The proof of Lemma 6 (Case 2) uses it to recognize a minimum-weight base of a minor.
--
--   **Formalization Note** The paper's "$C \subset E$" is read as $C \subseteq E$.
--
--   Differences from the source:
--   - reading: for every cut C ⊂ E / every circuit C ⊂ E → every cocircuit / circuit C ⊆ E; reason: the paper uses ⊂ for subsets (e.g. "for every F ⊂ E" in the proof of Theorem 24); the strict reading omits the cut C = E of a rank-one matroid without loops, where condition 2 is needed for the equivalence
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, Theorem 22 and the sentence "Let B be a base of M" before it, p.20

import Mathlib
import Definitions.Def_MatroidOptGame_IsMinWeightBase

namespace MatroidOptGame

/-- **Theorem 22 (matroid red-blue rules).** Let `B` be a base of `M`. The following are
equivalent:
1. `B` is a minimum-weight base of `M` with respect to `w`;
2. for every `e ∈ B`, every cut `C` with `C ∩ B = {e}` and every `f ∈ C`, `w(e) ≤ w(f)`;
3. for every circuit `C` with `|C ∖ B| = 1`, writing `{f} = C ∖ B`, every `e ∈ C` has
   `w(e) ≤ w(f)`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, Theorem 22 and the sentence "Let B be a base of M" before it, p.20.

**Formalization Note.** A cut is a cocircuit (`Matroid.IsCocircuit`, p.19). The paper's "C ⊂ E"
is read as `C ⊆ E` (the paper uses `⊂` for subsets, e.g. "for every F ⊂ E" in the proof of
Theorem 24); a strict reading would drop the cut `C = E` of a rank-one matroid, where the
equivalence needs it. `|C ∖ B| = 1` with `{f} = C ∖ B` is stated as `C ∖ B = {f}`. -/
theorem theorem_22 {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α) (w : α → ℕ)
    (B : Finset α) (hB : M.IsBase (B : Set α)) :
    List.TFAE
      [IsMinWeightBase M w B,
       ∀ e ∈ B, ∀ K : Set α, M.IsCocircuit K → K ∩ (B : Set α) = {e} → ∀ f ∈ K, w e ≤ w f,
       ∀ (C : Set α) (f : α), M.IsCircuit C → C \ (B : Set α) = {f} → ∀ e ∈ C, w e ≤ w f] := by sorry

end MatroidOptGame
