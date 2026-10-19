-- Prove2me | Theorems.Thm_OAI_Erdos3_vectorDesignatedRankFailureProbability_affineSpatial_mean_le_s2
-- name    : OAI.Erdos3.vectorDesignatedRankFailureProbability_affineSpatial_mean_le_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:42:55.480721+00:00
-- url     : https://prove2.me/theorems/11114c50-b840-47e0-9184-2a89b4c5b974
-- title:
--   Averaged over affine spatial coefficients, the designated vector rank failure probability modulo a prime power is small
-- statement:
--   Let $A$, $B$, $I$ be finite types with decidable equality, $p$ a prime, and $a, n, s$ natural numbers with $a > 0$, $s \ge 2$ and $n + 1 \le s$; write $R = \mathbb{Z}/p^a$. Let $\mathrm{stride} : B \to \mathbb{N}$ and let `spatial` be a predicate on $B$ such that for every $b$ with $\mathrm{spatial}(b)$: $n = 0$, $\mathrm{stride}(b) > 0$, and $2 v_p(\mathrm{stride}(b)) \le a$, where $v_p$ is the exponent of $p$ in the factorization. Let $\mathrm{offset} : B \to A \to R$. Let $S(b, i) \subseteq I$ be finite sets with $\lvert S(b, i)\rvert = n + 1$ for all $b \in B$, $i \in A$, and with $S(b, i)$ and $S(b, j)$ disjoint whenever $i \ne j$; let $Q(b)$ be multivariate polynomials in the variables $I$ over $R$; and let $w : B \to R$ with $w(b)$ a unit for at least one $b$.
--
--   For a coefficient array $c : B \to A \to R$, `vectorDesignatedRankFailureProbability (p^a) n S Q w c` is, by OpenAI's definition, the probability over a uniform $u \in (R^I)^n$ that the linear part (the coefficients of the degree-one monomials $X_i$) of the $n$-fold iterated difference with steps $u$ of the polynomial
--   $$\sum_{b \in B} w(b)\Bigl(Q(b) + \sum_{i \in A} c(b, i) \prod_{x \in S(b, i)} X_x\Bigr)$$
--   vanishes. Let `affineSpatialCoefficients spatial stride offset c` be the array that equals $\mathrm{stride}(b)\, c(b, i) + \mathrm{offset}(b, i)$ at spatial $b$ and $c(b, i)$ otherwise.
--
--   Then the mean, over a uniformly random array $c : B \to A \to R$, of `vectorDesignatedRankFailureProbability (p^a) n S Q w (affineSpatialCoefficients spatial stride offset c)` is at most
--   $$\Bigl(s \cdot (p^a)^{-\kappa_s}\Bigr)^{\lvert A\rvert}, \qquad \kappa_s = \texttt{modularRankSmallBallExponent}\ s = 2^{1 - s}.$$
--
--   Lean: `OAI.Erdos3.vectorDesignatedRankFailureProbability_affineSpatial_mean_le_s2`, which states OpenAI's `OAI.Erdos3.vectorDesignatedRankFailureProbability_affineSpatial_mean_le` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedModularRankAffineProbability.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B113` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedModularRankAffineProbability.lean (declaration OAI.Erdos3.vectorDesignatedRankFailureProbability_affineSpatial_mean_le)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B113

section

namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem vectorDesignatedRankFailureProbability_affineSpatial_mean_le_s2
    {A B I : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] {p a n s : ℕ} {stride : B → ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) (hs : 2 ≤ s) (hns : n + 1 ≤ s)
    (spatial : B → Prop) (hspatial : ∀ b, spatial b → n = 0)
    (hstride : ∀ b, spatial b → 0 < stride b)
    (hdeep : ∀ b, spatial b → 2 * (stride b).factorization p ≤ a)
    (offset : B → A → ZMod (p ^ a))
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod (p ^ a)))
    (hcard : ∀ b i, (S b i).card = n + 1)
    (hdisjoint : ∀ b, Pairwise (fun i j => Disjoint (S b i) (S b j)))
    (w : B → ZMod (p ^ a)) (hprimitive : ∃ b, IsUnit (w b)) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod (p ^ a))).mean
      (fun c => vectorDesignatedRankFailureProbability (p ^ a) n S Q w
        (affineSpatialCoefficients spatial stride offset c)) ≤
      ((s : ℝ) * ((p : ℝ) ^ a) ^ (-modularRankSmallBallExponent s)) ^ Fintype.card A := by
  sorry

end Erdos3

end

end OAI
end
