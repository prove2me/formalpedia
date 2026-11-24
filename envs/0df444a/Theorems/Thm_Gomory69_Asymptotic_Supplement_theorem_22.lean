-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_Supplement_theorem_22
-- name    : Gomory69.Asymptotic.Supplement.theorem_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:28:21.076008+00:00
-- url     : https://prove2.me/theorems/1025fe03-9ebc-4bb1-af3a-b159d04e40f0
-- title:
--   THEOREM 22 — Dominance of the character inequalities at the fixed target (corrected: trivial faces t(ψg₀) ≥ 0 excluded)
-- statement:
--   Let $G$ be a finite Abelian group of order $D$, let $H$ be cyclic of the same order, let $\psi:G\to H$ be any additive character and fix $g_0\in G$. Let $t'\in\mathbb R^{G^+}$ be componentwise nonnegative. Extend every coefficient vector on $H^+$ by $\pi(0)=0$.
--
--   Suppose that, for every facet $(\pi,\pi_0)$ of $P(H,\psi g_0)$,
--   $$\sum_{g\in G^+}\pi(\psi g)t'(g)\ge\pi_0.$$
--   Then for every $h_0\in H$ and every facet $(\pi,\pi_0)$ of $P(H,h_0)$ with $\pi_0>0$ or $\pi(\psi g_0)=0$,
--   $$\sum_{g\in G^+}\pi(\psi g)t'(g)\ge\pi(\psi g_0).$$
--   Neither character surjectivity nor integrality of $t'$ is assumed. Both zero-target cases are included. The constant in the conclusion is the coefficient at $\psi g_0$, not the other facet's right-hand side.
--
--   The paper asserts the conclusion for all faces of every $P(H,h_0)$. That is false for the trivial faces $a\,t(\psi g_0)\ge0$ ($a>0$, faces by THEOREM 16 when $|H|\ge3$): for $G=H=\mathbb Z/3$, $\psi=\mathrm{id}$, $g_0=2$, $t'=2u(1)$ (an integer solution, so it satisfies every facet of $P(H,2)$) and $\pi=u(2)$, $\pi_0=0$, the printed conclusion reads $0\ge1$. The proof on p. 504 uses subadditivity of $\pi$, which faces with $\pi_0>0$ have and the trivial faces do not. The excluded faces are exactly the positive multiples of $t(\psi g_0)\ge0$; every other face is covered.
--
--   This states precisely which full family of character inequalities dominates the inequalities from other targets.
--
--   Differences from the source:
--   - correction: the conclusion is printed for all faces (π, π₀) of every P(ℋ, h₀) → it is stated for every face with π₀ > 0 or π(ψg₀) = 0, i.e. all faces except the positive multiples of t(ψg₀) ≥ 0; reason: for those trivial faces the printed conclusion is false (ZMod 3, ψ = id, g₀ = 2, t′ = 2u(1), π = u(2): 0 ≥ 1); the proof on p. 504 relies on subadditivity, which only faces with π₀ > 0 satisfy
--   - encoding: characters map to a cyclic group isomorphic to fractions with denominator D modulo one → an arbitrary additive homomorphism to a cyclic group of the same finite cardinal; reason: pp. 500–502 identify these additive realizations; this is not an onto map assumption
--   - encoding: pi(psi g) in the inequalities → reuse the published liftCoeff, which extends pi by zero before composition; reason: the same formula is used in the published lifting interface; no complex or multiplicative character convention is imported
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), DOI 10.1016/0024-3795(69)90017-2, p. 503, THEOREM 22

import Mathlib
import Definitions.Def_Gomory69_Lifting_Lift

namespace Gomory69.Asymptotic.Supplement

/-- Corrected THEOREM 22: the conclusion is asserted for every face of every `P(ℋ, h₀)` except
the positive multiples of the trivial face `t(ψ g₀) ≥ 0`, for which it fails. -/
theorem theorem_22 {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H] [IsAddCyclic H]
    (hcard : Fintype.card G = Fintype.card H) (ψ : G →+ H) (g₀ : G)
    (t : Gomory69.Lifting.Plus G → ℝ) (ht : ∀ g, 0 ≤ t g)
    (hall : ∀ (π : Gomory69.Lifting.Plus H → ℝ) (π₀ : ℝ),
      Gomory69.Lifting.IsFace H (ψ g₀) π π₀ →
      π₀ ≤ Gomory69.Lifting.liftCoeff ψ π ⬝ᵥ t) :
    ∀ (h₀ : H) (π : Gomory69.Lifting.Plus H → ℝ) (π₀ : ℝ),
      Gomory69.Lifting.IsFace H h₀ π π₀ →
      (0 < π₀ ∨ Gomory69.Lifting.ext π (ψ g₀) = 0) →
      Gomory69.Lifting.ext π (ψ g₀) ≤ Gomory69.Lifting.liftCoeff ψ π ⬝ᵥ t := by sorry

end Gomory69.Asymptotic.Supplement
