-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_low_degree_lsi_criterion
-- name    : MatchingNearLinear.Glauber.low_degree_lsi_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:54:40.419572+00:00
-- url     : https://prove2.me/theorems/73572624-198b-425f-bc71-06498759fc38
-- title:
--   Proposition 3.1 — Low-degree approximation criterion for LSI
-- statement:
--   There is a universal constant $c>0$ with the following property. Let $p$ be a positive probability on any finite support $\Omega$ with at least two states, and let $P$ be any irreducible $p$-reversible stochastic kernel. For an integer $r\ge1$, let $V_0\subseteq\cdots\subseteq V_r$ be real linear subspaces, with $V_0$ the constants and $V_r=L^2(p)$. Write $\Pi_j$ for their weighted orthogonal projections. If $A,\Lambda\ge1$ satisfy
--
--   $$\mathcal E_P(f,f)\ge\frac{j+1}{A}\|f-\Pi_jf\|_2^2\quad(j<r),\qquad \|g\|_\infty\le e^{\Lambda j/2}\|g\|_2\quad(g\in V_j,\ j\le r),$$
--
--   then $\alpha_{\rm LS}^{-1}\le cA\Lambda$. The first inequality holds for every real function $f$. No subset structure or invariance of $V_j$ under $P$ is required. This criterion converts approximation and norm estimates into a full LSI.
--
--   Differences from the source:
--   - encoding: an upper bound on the inverse optimal log-Sobolev or modified log-Sobolev constant → the corresponding functional inequality with the asserted coefficient; reason: these are equivalent for the source irreducible finite kernels and avoid default values for invalid extrema
--   - encoding: weighted L2 orthogonal projection → the unique member of the subspace satisfying all weighted orthogonality equations, selected noncomputably; reason: a positive law on a finite support guarantees existence and uniqueness; the invalid-weight fallback is never used
--   - encoding: parameter-uniform or universal big-O bounds → a positive existential constant before all instance parameters; secondary asymptotic clauses quantify fixed bounds first; reason: this is the precise uniform meaning of the source asymptotic notation
--   - encoding: a law with finite support Omega having at least two states → an arbitrary finite type with at least two elements carrying a strictly positive probability mass function; reason: the type plays the role of Omega, so every source instance is one Lean instance and conversely
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Proposition 3.1, printed p. 10 (PDF p. 12); continues on printed p.11 (PDF p.13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_FiniteAnalysis

set_option autoImplicit false

namespace MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/

theorem low_degree_lsi_criterion :
    ∃ c : ℝ, 0 < c ∧ ∀ (α : Type) [Fintype α] [DecidableEq α],
    2 ≤ Fintype.card α → ∀ (p : α → ℝ) (P : Matrix α α ℝ),
    PositiveLaw p → MarkovMixing.IsStochastic P → MarkovMixing.Irreducible P →
    MarkovMixing.DetailedBalance P p →
    ∀ (r : ℕ), 1 ≤ r → ∀ (V : ℕ → Submodule ℝ (α → ℝ)),
    V 0 = constantSpace → V r = ⊤ → (∀ j, j < r → V j ≤ V (j+1)) →
    ∀ A Λ : ℝ, 1 ≤ A → 1 ≤ Λ →
    (∀ j, j < r → ∀ f : α → ℝ,
      energy p P f f ≥ (((j:ℝ)+1)/A) * normSq p (f - projection p (V j) f)) →
    (∀ j, j ≤ r → ∀ g ∈ V j, normInfinity g ≤ Real.exp (Λ*j/2) * normTwo p g) →
    LSIBound p P (c*A*Λ) := by sorry

end MatchingNearLinear.Glauber
