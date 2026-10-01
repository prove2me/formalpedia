-- Prove2me | Theorems.Thm_MoreauProx_Decomposition_conj_gammaZero_and_conj_conj
-- name    : MoreauProx.Decomposition.conj_gammaZero_and_conj_conj
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:11:40.475905+00:00
-- url     : https://prove2.me/theorems/fdbace58-de5d-40b3-bcb5-67087aa1385e
-- title:
--   §2.b — the dual of f ∈ Γ₀(H) lies in Γ₀(H), and its dual is f
-- statement:
--   Let $H$ be a real Hilbert space and $f \in \Gamma_0(H)$. Let $g = f^{*}$ be the dual function of $f$, $g(y) = \sup_{x\in H}[(x\mid y) - f(x)]$. Then
--
--   1. $g \in \Gamma_0(H)$;
--   2. $f$ is the dual function of $g$: for every $x \in H$,
--   $$ f(x) = \sup_{y \in H}\,\big[(x \mid y) - g(y)\big]. $$
--
--   Together these say that $f \mapsto f^{*}$ is an involution of $\Gamma_0(H)$ (the Fenchel–Moreau theorem). It is what makes the relation "$f$ and $g$ are dual to each other" symmetric, and what makes $\mathrm{prox}_g$ meaningful in Moreau's decomposition theorem.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), pp. 276–277, §2.b (after (2.2))

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality

namespace MoreauProx.Decomposition

open scoped InnerProductSpace

/-- Moreau 1965, §2.b, p. 276: the dual of `f ∈ Γ₀(H)` belongs to `Γ₀(H)`, and `f` is the
dual of its dual. -/
theorem conj_gammaZero_and_conj_conj {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → EReal) (hf : GammaZero f) :
    GammaZero (conj f) ∧ conj (conj f) = f := by sorry

end MoreauProx.Decomposition
