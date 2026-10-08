-- Prove2me | Theorems.Thm_KarpPapadimitriou_Generator_system4_iff_decision
-- name    : KarpPapadimitriou.Generator.system4_iff_decision
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:41:36.619211+00:00
-- url     : https://prove2.me/theorems/da637d63-3fdf-4a24-8479-10bc186c9255
-- title:
--   p. 10, system (4) — feasibility is membership in D(C)
-- statement:
--   Let $G$ be a generator for $C$, let $z\in L$, let $c\in\mathbb Z^{n(z)}$, and let $k\in\mathbb Z$. System (4) consists of $c\cdot x\ge k$ and all inequalities $f\cdot x\le g$ in $F_G(C)$ for this $z$. It satisfies
--   $$\exists x\in\mathbb Q^{n(z)}\;\bigl(c\cdot x\ge k\ \land\ \forall\langle z,f,g\rangle\in F_G(C),\ f\cdot x\le g\bigr)\quad\Longleftrightarrow\quad \langle z,c,k\rangle\in D(C).$$
--
--   This is the optimization-to-feasibility equivalence on which the decision algorithm operates.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 10, proof of Theorem 2, system (4)

import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_Oracle

namespace KarpPapadimitriou.Generator

/-- System (4) is feasible precisely when the encoded threshold instance belongs to `D(C)`. -/
theorem system4_iff_decision (C : COP) (gen : Oracle C)
    (hgen : IsGenerator C gen) (z : List Bool) (hz : z ∈ C.L)
    (c : Fin (C.n z) → ℤ) (k : ℤ) :
    (∃ x : Fin (C.n z) → ℚ,
      (k : ℚ) ≤ dotQ c x ∧
      ∀ f g, (⟨z, (f, g)⟩ : Triple C) ∈ FG C gen → dotQ f x ≤ (g : ℚ)) ↔
      encDInput z c k ∈ DLang C := by sorry

end KarpPapadimitriou.Generator
