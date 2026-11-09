-- Prove2me | Theorems.Thm_MinCostMaj_lemma_basic_2_absorption
-- name    : MinCostMaj.lemma_basic_2_absorption
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:19:33.164232+00:00
-- url     : https://prove2.me/theorems/44dedcc8-5cf7-4c7c-bc72-0c3929b16081
-- title:
--   Lemma "Basic 2-absorption facts" — 2-absorbing sets meet, and absorption propagates along patterns
-- statement:
--   Let $I$ be a finite arc-consistent instance (opposite readings) and $\{f_x\}_x$ a conservative commutative binary polymorphism of $I$.
--
--   1. If $B,C\subseteq A_x$ both 2-absorb $A_x$, then $B\cap C\neq\emptyset$.
--   2. If $B\subseteq A_x$ 2-absorbs $A_x$ and $p$ is a pattern from $x$ to $y$, then $B+p$ 2-absorbs $A_y$.
--
--   These two facts are the engine of the proof of Proposition A.4.
--
--   Differences from the source:
--   - reading: instances of CSP(A) on a variable set V → finite variable and value types (`Finite V`, `Finite D`) with the opposite-readings convention `IsSymm` as a hypothesis; reason: instances are finite inputs and §3 assumes R_vu holds the opposite readings of R_uv for every instance
--   - encoding: a pattern R_1,…,R_n along u = w_0,…,w_n = v → the start u and the list of steps (R_i, w_i); concatenation is list append; reason: same patterns
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Lemma "Basic 2-absorption facts", p.18 (PDF p.19)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst
import Definitions.Def_MinCostMaj_Pattern
import Definitions.Def_MinCostMaj_BinPol

namespace MinCostMaj

/-- **Lemma "Basic 2-absorption facts"**, p.18 (PDF p.19).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Lemma "Basic 2-absorption facts", p.18: "Let I be arc-consistent and let {fx}x be a
conservative commutative binary polymorphism of I.
• If B, C ⊆ Ax both 2-absorb Ax, then B ∩ C ≠ ∅.
• If B ⊆ Ax 2-absorbs Ax and p is a pattern from x to y, then B + p 2-absorbs Ay."

**Formalization Note.** Both bullets, as a conjunction. `B + p` is `plusPat I y B l`. Finite
instance with §3's opposite-readings convention. -/
theorem lemma_basic_2_absorption {V D : Type*} [Finite V] [Finite D] (I : BinInst V D)
    (hS : I.IsSymm) (hAC : I.IsArcConsistent) (f : V → D → D → D)
    (hf : I.IsConsCommBinPol f) :
    (∀ x (B C : Set D), I.TwoAbsorbs f x B → I.TwoAbsorbs f x C → (B ∩ C).Nonempty) ∧
    (∀ x y (B : Set D) (l : List (Set (D × D) × V)), IsPat I.rels x l y →
      I.TwoAbsorbs f x B → I.TwoAbsorbs f y (plusPat I y B l)) := by sorry

end MinCostMaj
