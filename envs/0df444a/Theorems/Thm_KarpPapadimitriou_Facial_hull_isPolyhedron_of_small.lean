-- Prove2me | Theorems.Thm_KarpPapadimitriou_Facial_hull_isPolyhedron_of_small
-- name    : KarpPapadimitriou.Facial.hull_isPolyhedron_of_small
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:28:51.783097+00:00
-- url     : https://prove2.me/theorems/1f538be3-c8b4-4ac0-9bac-dd6b367b047d
-- title:
--   p. 5 — a small facial description makes every CH(S(z)) a convex polyhedron
-- statement:
--   Let $C$ be a combinatorial optimization problem and $F(C)$ a small facial description of $C$. Then for every $z\in L$:
--
--   1. only finitely many triples of $F(C)$ have first entry $z$;
--   2. $\mathrm{CH}(S(z))$ is a convex polyhedron, i.e. there are finitely many pairs $(a_1,b_1),\dots,(a_m,b_m)\in\mathbb Q^{n(z)}\times\mathbb Q$ with
--   $$\mathrm{CH}(S(z))=\{x\in\mathbb Q^{n(z)} : a_i\cdot x\le b_i,\ i=1,\dots,m\}.$$
--
--   This is the remark that follows the definition of small facial descriptions: smallness bounds the coefficients, so only finitely many inequalities can be listed for each input, and the convex hull is the intersection of finitely many half-spaces.
--
--   **Formalization Note** Part 1 is the reason the paper's remark holds and is stated explicitly. A half-space is written $\{x : a\cdot x\le b\}$ with rational data; $m=0$ gives the whole space.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 5, remark after the definition of small facial descriptions

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription

namespace KarpPapadimitriou.Facial

theorem hull_isPolyhedron_of_small (C : COP) (F : Triples C)
    (hF : IsFacialDescription C F) (hs : IsSmall C F) (z : List Bool) (hz : z ∈ C.L) :
    {fg : (Fin (C.n z) → ℤ) × ℤ |
        (⟨z, fg⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F}.Finite ∧
      ∃ H : Finset ((Fin (C.n z) → ℚ) × ℚ),
        hull C z = {x : Fin (C.n z) → ℚ | ∀ h ∈ H, h.1 ⬝ᵥ x ≤ h.2} := by sorry

end KarpPapadimitriou.Facial
