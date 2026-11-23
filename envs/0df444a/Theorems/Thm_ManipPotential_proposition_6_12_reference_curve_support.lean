-- Prove2me | Theorems.Thm_ManipPotential_proposition_6_12_reference_curve_support
-- name    : ManipPotential.proposition_6_12_reference_curve_support
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:33:38.635414+00:00
-- url     : https://prove2.me/theorems/935f7485-9127-4399-a374-1f2e7fbf141b
-- title:
--   Lemma 6.10 controls winners near the reference curve
-- statement:
--   Assume $m\ge3$, let $g$ satisfy the axioms of Lemma 6.2, and suppose the common junction $P=G(z_0+t\rho v)$ has every coordinate greater than $1$. For $\rho>0$, $0\le t\le1$, and $\varepsilon=\rho/(4\kappa)<\tfrac12$, every rational profile $Q$ satisfying
--   $$
--   \|Q-B_\rho(t)\|_\infty<\frac{\varepsilon}{4}
--   $$
--   elects either $c_i$ or $c_j$. More precisely, at $t=0$ it elects $c_i$, and at $t=1$ it elects $c_j$.
--
--   This is exactly the application of Lemma 6.10 in Step 1 of Proposition 6.12. The cyclic increment in $B_\rho(t)$ is nonnegative, has total weight $\rho>\kappa\varepsilon$, and is supported in $\{i,j\}$, a proper subset because $m\ge3$; at the endpoints its support is the corresponding singleton. The coordinate bound $P_r>1$ and $\varepsilon<\tfrac12$ supply the remaining condition $\varepsilon<\tfrac12\min_rP_r$.
--
--   **Formalization Note** The explicit hypothesis $\varepsilon<\tfrac12$ is necessary for Lemma 6.10 and is guaranteed by the separate small-$\rho$ path-assembly lemma.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Proposition 6.12, Step 1, p.37, application of Lemma 6.10 to $B_\rho(t)$; Lemma 6.10, Eq. (13), pp.32–33.

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_referenceCurve

namespace ManipPotential

/-- Lemma 6.10 applied along the reference curve: nearby rational profiles elect only `i` or `j`,
with the indicated endpoints. -/
theorem proposition_6_12_reference_curve_support {m : ℕ} [NeZero m]
    (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m) (hg : GAxioms K g)
    (G : ((ExtRanking m → ℝ) × ℝ) → (Ranking m → ℝ))
    (z₀ v : ((ExtRanking m → ℝ) × ℝ)) (i j : Fin m) (hij : i ≠ j)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hε : ρ / (4 * kappa m K) < 1 / 2) (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (Q : Ranking m → ℚ)
    (hP : IsCommonJunction g (G (z₀ + (t * ρ) • v)))
    (hPpos : ∀ r, 1 < G (z₀ + (t * ρ) • v) r)
    (hQ : ‖(fun r => (Q r : ℝ)) - referenceCurve K G z₀ v i j ρ t‖ <
      (ρ / (4 * kappa m K)) / 4) :
    (g Q = i ∨ g Q = j) ∧ (t = 0 → g Q = i) ∧ (t = 1 → g Q = j) := by sorry
