-- Prove2me | Theorems.Thm_OnlineConvexOpt_Blackwell_blackwell_approachability_sufficiency_v2
-- name    : OnlineConvexOpt.Blackwell.blackwell_approachability_sufficiency_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:53.655648+00:00
-- url     : https://prove2.me/theorems/db09c73a-017a-4a0f-a1f9-2c875168e250
-- title:
--   Theorem 13.4 (sufficiency) — Blackwell approachability for biaffine continuous vector games on compact convex sets
-- statement:
--   **Statement (Theorem 13.4, sufficiency direction).** Let $K_1\subseteq E_1$, $K_2\subseteq E_2$ be nonempty compact convex decision sets in real normed spaces, and let $u:E_1\times E_2\to\mathbb R^d$ be a vector payoff that is jointly continuous on $K_1\times K_2$ and biaffine there (affine in $x\in K_1$ for each $y\in K_2$ and affine in $y\in K_2$ for each $x\in K_1$, as for the mixed extension $u(x,y)=\mathbb E_{i\sim x,j\sim y}[u(i,j)]$ of Definition 13.1). Let $S\subseteq\mathbb R^d$ be closed, bounded and convex. If for every $y\in K_2$ there is $x\in K_1$ with $u(x,y)\in S$, then $S$ is approachable (Definition 13.3): there is a non-anticipating strategy $x_t=A(y_1,\dots,y_{t-1})\in K_1$ such that for every sequence $y_t\in K_2$, $\mathrm{Dist}\bigl(\frac1T\sum_{t\le T}u(x_t,y_t),S\bigr)\to0$.
--
--   **Formalization Note.** The retired statement took an arbitrary payoff map $u:E_1\to E_2\to F$ on arbitrary normed spaces, exactly as Definition 13.2 is printed, and was refuted: for a discontinuous $u$ (e.g. $u(x,y)=\mathbf 1[x\ne y]$ on $[0,1]^2$) the adversary out-guesses every non-anticipating strategy. The book's proof needs structure it never writes down: Lemma 13.6 applies Sion's minimax theorem to $(x,y)\mapsto w^\top u(x,y)$ on $K_1\times K_2$, which requires convexity–concavity (biaffinity suffices), continuity and compactness, and Theorem 13.7 runs an OCO algorithm on the unit ball of $\mathbb R^d$ with the losses $w\mapsto w^\top u_t-h_S(w)$, which needs bounded payoffs (continuity on a compact set) and a Euclidean payoff space. These standing assumptions — the ones Definition 13.1's finite games satisfy — are now explicit: compact convex nonempty $K_1,K_2$, payoff values in $\mathbb R^d$, joint continuity and biaffinity of $u$ on $K_1\times K_2$. Only the sufficiency direction is stated, as before.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 209, Theorem 13.4 (PDF p. 231) — with the structure of the payoff (biaffine, continuous; compact convex decision sets; Euclidean payoff space) that Definition 13.2 omits but Lemma 13.6's minimax step and Theorem 13.7's OCO step require

import Mathlib
import Definitions.Def_OnlineConvexOpt_Blackwell_Approachability

namespace OnlineConvexOpt.Blackwell

/-- Theorem 13.4, Blackwell's Approachability Theorem — **sufficiency direction only** (Hazan,
*Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 209, PDF p. 231).
For a generalized vector game `K1, K2, u` (Definition 13.2: `K1`, `K2` nonempty, bounded,
convex and closed — here compact — decision sets; `u` a vector payoff with values in `ℝ^d`,
biaffine and jointly continuous on `K1 × K2`, as for the mixed extension of Definition 13.1's
finite games, `u(x,y) = E_{i∼x,j∼y}[u(i,j)]`), if `∀y∈K2, ∃x∈K1, u(x,y)∈S`, then the closed,
bounded, convex set `S ⊆ ℝ^d` is approachable (Definition 13.3). The book's theorem is a
biconditional; it proves, and this statement drafts, only the sufficiency direction.

Corrected version: the retired statement took an arbitrary payoff map `u : E1 → E2 → F` on
arbitrary normed spaces, for which the theorem is false (a discontinuous `u` lets the adversary
out-guess every non-anticipating strategy). The proof's minimax step (Lemma 13.6, Sion's
theorem applied to `w^⊤u(x,y)`) needs `u` convex-concave and continuous on compact convex sets,
and the OCO step (Theorem 13.7 with online gradient descent on the unit ball of `ℝ^d`) needs
the payoffs bounded and the payoff space Euclidean; these unwritten standing assumptions of
Definition 13.2 are now explicit. -/
theorem blackwell_approachability_sufficiency_v2
    {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2]
    [NormedSpace ℝ E2] {d : ℕ}
    (K1 : Set E1) (K2 : Set E2) (u : E1 → E2 → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSconv : Convex ℝ S) (hSbdd : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hK1cpt : IsCompact K1) (hK1conv : Convex ℝ K1) (hK1ne : K1.Nonempty)
    (hK2cpt : IsCompact K2) (hK2conv : Convex ℝ K2) (hK2ne : K2.Nonempty)
    (hucont : ContinuousOn (fun p : E1 × E2 => u p.1 p.2) (K1 ×ˢ K2))
    (huaffx : ∀ y ∈ K2, ∀ x₁ ∈ K1, ∀ x₂ ∈ K1, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      u (a • x₁ + b • x₂) y = a • u x₁ y + b • u x₂ y)
    (huaffy : ∀ x ∈ K1, ∀ y₁ ∈ K2, ∀ y₂ ∈ K2, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      u x (a • y₁ + b • y₂) = a • u x y₁ + b • u x y₂)
    (hcond : ∀ y ∈ K2, ∃ x ∈ K1, u x y ∈ S) :
    IsApproachable K1 K2 u S := by sorry

end OnlineConvexOpt.Blackwell
