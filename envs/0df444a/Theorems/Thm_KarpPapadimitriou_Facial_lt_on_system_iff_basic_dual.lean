-- Prove2me | Theorems.Thm_KarpPapadimitriou_Facial_lt_on_system_iff_basic_dual
-- name    : KarpPapadimitriou.Facial.lt_on_system_iff_basic_dual
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:28:56.266192+00:00
-- url     : https://prove2.me/theorems/76a94a34-0250-4f52-a76d-9605ab7845e4
-- title:
--   p. 8, proof of Theorem 1, (iii)⇔(vi) — a nonsingular n(z)×n(z) row selection of F(C) certifies optimal value < k
-- statement:
--   Let $C$ be a combinatorial optimization problem, $F(C)$ a small facial description of $C$, and $z\in L$ with $S(z)\neq\emptyset$. Let $c\in\mathbb Z^{n(z)}$ and $k\in\mathbb Z$. Then the following are equivalent:
--
--   (iii) the program $\max\ c\cdot x$ subject to $f\cdot x\le g$ for all $\langle z,f,g\rangle\in F(C)$ has optimal value $<k$, i.e. every feasible $x\in\mathbb Q^{n(z)}$ has $c\cdot x<k$;
--
--   (vi) there exist an $n(z)\times n(z)$ integer matrix $\mathbf F=(f_{ij})$ and an integer vector $g\in\mathbb Z^{n(z)}$ such that
--   $$\langle z,(f_{i1},f_{i2},\dots,f_{in(z)}),g_i\rangle\in F(C),\qquad i=1,2,\dots,n(z),$$
--   $\mathbf F$ is nonsingular, and the (therefore unique) solution $y\in\mathbb Q^{n(z)}$ of the system
--   $$y^{T}\mathbf F=c$$
--   is nonnegative and satisfies $y^{T}g<k$.
--
--   In the paper this equivalence passes through (iv) "the dual of program (I) has optimal value $<k$" and (v) "the dual of program (I) has a basic feasible solution of value $<k$"; condition (vi) is the explicit form of (v), a basic dual solution supported on $n(z)$ linearly independent inequalities. It is the short certificate that Algorithm B guesses to recognize the complement of $D(C)$.
--
--   **Formalization Note** The hypothesis $S(z)\neq\emptyset$ is tacit in the paper's proof and is needed: for $n(z)=1$ and the description $\{x\le-1,\ -x\le0\}$ of the empty hull, $c=-1$ and $k=0$ satisfy (iii) (vacuously), while the only nonsingular $1\times1$ selection with a nonnegative solution of $y^T\mathbf F=c$ is the row $-x\le 0$, with $y=1$ and $y^Tg=0\not<0$. "Unique solution" is formalized as nonsingularity of $\mathbf F$ (determinant $\neq0$), which is how Algorithm B (step (iv)) checks it. Intermediate conditions (iv) and (v) are not stated separately.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 8, proof of Theorem 1, (iii)⇔(iv)⇔(v)⇔(vi)

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription

namespace KarpPapadimitriou.Facial

theorem lt_on_system_iff_basic_dual (C : COP) (F : Triples C) (hF : IsFacialDescription C F)
    (hs : IsSmall C F) (z : List Bool) (hz : z ∈ C.L) (hS : (C.S z).Nonempty)
    (c : Fin (C.n z) → ℤ) (k : ℤ) :
    (∀ x : Fin (C.n z) → ℚ,
        (∀ (f : Fin (C.n z) → ℤ) (g : ℤ),
            (⟨z, (f, g)⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F →
              (fun j => (f j : ℚ)) ⬝ᵥ x ≤ (g : ℚ)) →
          (fun j => (c j : ℚ)) ⬝ᵥ x < (k : ℚ)) ↔
      ∃ (fm : Matrix (Fin (C.n z)) (Fin (C.n z)) ℤ) (g : Fin (C.n z) → ℤ),
        (∀ i, (⟨z, (fm i, g i)⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F) ∧
          fm.det ≠ 0 ∧
          ∃ y : Fin (C.n z) → ℚ,
            Matrix.vecMul y (fm.map (fun a : ℤ => (a : ℚ))) = (fun j => (c j : ℚ)) ∧
              0 ≤ y ∧ y ⬝ᵥ (fun i => (g i : ℚ)) < (k : ℚ) := by sorry

end KarpPapadimitriou.Facial
