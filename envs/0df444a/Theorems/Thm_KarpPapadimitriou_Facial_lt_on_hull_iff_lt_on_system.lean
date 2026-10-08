-- Prove2me | Theorems.Thm_KarpPapadimitriou_Facial_lt_on_hull_iff_lt_on_system
-- name    : KarpPapadimitriou.Facial.lt_on_hull_iff_lt_on_system
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:29:02.497435+00:00
-- url     : https://prove2.me/theorems/413a2eb9-42b6-4abc-8f2a-4789fd6b3d98
-- title:
--   p. 8, proof of Theorem 1, (ii)⇔(iii) — the hull may be replaced by the system f·x ≤ g, ⟨z,f,g⟩ ∈ F(C)
-- statement:
--   Let $C$ be a combinatorial optimization problem, $F(C)$ a facial description of $C$, $z\in L$, $c\in\mathbb Z^{n(z)}$ and $k\in\mathbb Z$. Then the following are equivalent:
--
--   (ii) the program $\max\ c\cdot x$ subject to $x\in\mathrm{CH}(S(z))$ has optimal value $<k$;
--
--   (iii) the program
--   $$\max\ c\cdot x\quad\text{subject to}\quad f\cdot x\le g\quad(\langle z,f,g\rangle\in F(C))\qquad\text{(I)}$$
--   has optimal value $<k$.
--
--   Here both are read as "every feasible $x\in\mathbb Q^{n(z)}$ has $c\cdot x<k$". The step is the point where the facial description enters the proof of Theorem 1.
--
--   **Formalization Note** As in step (i)⇔(ii), "optimal value $<k$" means that every feasible point has value $<k$.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 8, proof of Theorem 1, (ii)⇔(iii)

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription

namespace KarpPapadimitriou.Facial

theorem lt_on_hull_iff_lt_on_system (C : COP) (F : Triples C) (hF : IsFacialDescription C F)
    (z : List Bool) (hz : z ∈ C.L) (c : Fin (C.n z) → ℤ) (k : ℤ) :
    (∀ x ∈ hull C z, (fun j => (c j : ℚ)) ⬝ᵥ x < (k : ℚ)) ↔
      ∀ x : Fin (C.n z) → ℚ,
        (∀ (f : Fin (C.n z) → ℤ) (g : ℤ),
            (⟨z, (f, g)⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F →
              (fun j => (f j : ℚ)) ⬝ᵥ x ≤ (g : ℚ)) →
          (fun j => (c j : ℚ)) ⬝ᵥ x < (k : ℚ) := by sorry

end KarpPapadimitriou.Facial
