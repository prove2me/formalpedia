-- Prove2me | Theorems.Thm_MusicStreaming_Axioms_constant_weight
-- name    : MusicStreaming.Axioms.constant_weight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:16.976655+00:00
-- url     : https://prove2.me/theorems/037c9cd2-f1f8-44f5-b645-0f0b38234c91
-- title:
--   Appendix, proof of Theorem 1(b), pp. 19–20 — under the axioms of (b) the weight ω(j, t.j) does not depend on j and t.j
-- statement:
--   Assume there are at least two artists. Let $I$ be a popularity index satisfying homogeneity, additivity and equal individual impact of similar users, and let $\omega$ be any positive weight system with $I=I^\omega$ (one exists by Theorem 1(a)). Then for all users $j,j'$ and all nonzero profiles $x,y\in\mathbb N^N$,
--   $$\omega(j,x)=\omega(j',y).$$
--
--   Writing $\lambda$ for this common value gives $I_i=\sum_{j\in M}\lambda t_{ij}=\lambda P_i$, which is the "only if" direction of Theorem 1(b).
--
--   **Formalization Note** The weight is determined by $I$ only at nonzero profiles, so only those are compared. Two artists are needed (the proof takes an artist $i'\neq i$ on p. 20); with one artist the user-centric index satisfies the axioms and is not a multiple of pro-rata. The argument uses users outside the given problem; user names range over all natural numbers.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, pp. 19–20, Appendix, proof of Theorem 1(b), from "We now prove that ω(j, t.j) does not depend on j and t.j" to "λ = ω(j, t.j)"

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

namespace MusicStreaming.Axioms

theorem constant_weight {n : ℕ} (hn : 2 ≤ n) (I : Index n) (hI : IsIndex I)
    (hH : Homogeneity I) (hA : Additivity I) (hE : EqualIndividualImpact I)
    (ω : ℕ → (Fin n → ℕ) → ℝ) (hω : ∀ j x, 0 < ω j x) (hIω : ∀ t, I t = weightedIndex ω t) :
    ∀ (j j' : ℕ) (x y : Fin n → ℕ), x ≠ 0 → y ≠ 0 → ω j x = ω j' y := by sorry

end MusicStreaming.Axioms
