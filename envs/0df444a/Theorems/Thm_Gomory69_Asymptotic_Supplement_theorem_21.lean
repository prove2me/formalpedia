-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_Supplement_theorem_21
-- name    : Gomory69.Asymptotic.Supplement.theorem_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:27:50.577466+00:00
-- url     : https://prove2.me/theorems/1408093b-2682-4f2e-a086-575c5152732d
-- title:
--   THEOREM 21 — Kernel facets combined with special cyclic quotient facets
-- statement:
--   Let $\psi:G\to H$ be a surjective homomorphism of finite Abelian groups, with $H$ cyclic and $|H|>2$. Let $K=\ker\psi$, let $g_0\in K$, let $(\pi_1,1)$ be any facet of $P(K,g_0)$, and let $\pi_2$ be any special normalized cyclic face as defined on p. 490. Then
--   $$\pi(g)=\begin{cases}\pi_1(g)&g\in K,\\\pi_2(\psi g)&g\notin K\end{cases}\quad\Longrightarrow\quad (\pi,1)\text{ is a facet of }P(G,g_0).$$
--   The kernel need not split off as a direct factor. Both even and odd quotient orders greater than two are admitted, and the kernel target may be zero.
--
--   This is the second quotient-based facet construction, complementary to the published descent theorem.
--
--   Differences from the source:
--   - encoding: the target lies in the kernel and coefficients are piecewise on and off it → the target has subtype ker psi and the combined coefficients evaluate pi1 on that subgroup; reason: subtype membership makes the source kernel condition explicit without restricting the homomorphism
--   - reading: pi2 is a special face → the special coefficients are given by a generator of full additive order and p divided by the group order; reason: varying the generator gives exactly the automorphism family on p. 490; no arbitrary quotient facet is substituted
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), DOI 10.1016/0024-3795(69)90017-2, p. 490, THEOREM 21

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_Supplement_SpecialFace

namespace Gomory69.Asymptotic.Supplement

theorem theorem_21 {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H] [IsAddCyclic H]
    (ψ : G →+ H) (honto : Function.Surjective ψ) (horder : 2 < Fintype.card H)
    (g₀ : ψ.ker) (π₁ : Gomory69.Lifting.Plus ψ.ker → ℝ)
    (hπ₁ : Gomory69.Lifting.IsFace ψ.ker g₀ π₁ 1)
    (π₂ : Gomory69.Lifting.Plus H → ℝ) (hspecial : IsSpecial π₂) :
    Gomory69.Lifting.IsFace G (g₀ : G) (combineCoeff ψ π₁ π₂) 1 := by sorry

end Gomory69.Asymptotic.Supplement
