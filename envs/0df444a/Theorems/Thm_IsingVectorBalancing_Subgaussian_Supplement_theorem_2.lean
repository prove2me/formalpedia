-- Prove2me | Theorems.Thm_IsingVectorBalancing_Subgaussian_Supplement_theorem_2
-- name    : IsingVectorBalancing.Subgaussian.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:19:21.261961+00:00
-- url     : https://prove2.me/theorems/57720ebe-b4eb-4eb4-b738-6c9fea7d0203
-- title:
--   Theorem 2 (corrected: endpoint mixing rate) — gap and complete worst-start mixing bound
-- statement:
--   Let $n\ge1$, let $v_i$ be an admissible family of unit-ball vectors and let $h\in\mathbb R^n$ be arbitrary. Put $\alpha_0=1-\max_i\|v_i\|_2^2$, and let $P_h$ be discrete-time random-scan heat-bath dynamics for the published law $\mu_h$. Then
--
--   $$\operatorname{gap}(P_h)\ge\alpha_0/n.$$
--
--   This includes the nonnegative gap bound at $\alpha_0=0$. If $\alpha_0>0$, then for every $0<\varepsilon<1$,
--
--   $$t_{\mathrm{mix},h}(\varepsilon)\le\left\lceil\frac n{\alpha_0}\left(\log\frac1\varepsilon+n\log2+2\|h\|_1+n^2\log\frac{2-\alpha_0}{\alpha_0}\right)\right\rceil.$$
--
--   Mixing is measured from the worst feasible initial configuration, with the source's strict total-variation threshold. The finite bound asserts successful convergence rather than using an empty natural infimum. The zero-field case is the printed model. The explicit proof bound corrects the printed asymptotic endpoint error and covers the entire positive-margin range. This companion theorem is not used in the proof of the mission's concentration goal.
--
--   Differences from the source:
--   - encoding: finite sets [n] and [q], real Euclidean vectors and finite expectations → Fin indices, EuclideanSpace, and finite sums; reason: the carriers and values are unchanged; Bool encodes the binary signs when present
--   - encoding: gap(P) bounded below on the feasible state space → the published finite Poincaré inequality with rates equal to the discrete transition matrix P; reason: its Laplacian is I−P on the support, so no time rescaling or irreducibility premise is introduced; singleton support is retained
--   - generalization: the printed zero-field statement of Theorem 2 → every real field h, with 2∥h∥₁ in the finite mixing bound; reason: the proof explicitly works with the tilted distribution (5); h=0 recovers the printed model
--   - correction: the uniform O((n/α₀)(log(1/ε)+n² log(α₀⁻¹))) mixing rate → the exact bound B(v,h,ε) from the proof, including n log 2 and exponent n²; reason: at v_i=0 and α₀=1 the printed rate is O(n) for ε=1/4, but the random-scan uniform sign cube has order n log n mixing; the counterexample is detailed in MODERATION_NOTES.md
--   - encoding: finite natural mixing times on convergent instances → extended natural mixing time, infinity when convergence fails; reason: finite upper bounds have their usual meaning and cannot be satisfied by an empty-infimum default
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), p. 2 (PDF 3), Theorem 2; proof p. 16 (PDF 17), explicit minimum-mass and ceiling bounds

import Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_VectorChain
import Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_StrictMixing
import Definitions.Def_SubsetConvFPRAS_ReversibleChain

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian.Supplement

/-- Theorem 2, p.2/PDF3, with arbitrary fields and the corrected exact mixing
bound from its proof p.16/PDF17. The printed uniform O-rate fails for v=0, α₀=1. -/
theorem theorem_2 {n d : ℕ} (hn : 0 < n) (v : Fin n → Vec d)
    (hv : Admissible v) (h : Fin n → ℝ) :
    SubsetConvFPRAS.HasPoincare (probability v h) (MarkovMixing.glauber (probability v h))
      (alpha0 v / (n : ℝ)) ∧
    (0 < alpha0 v → ∀ ε : ℝ, 0 < ε → ε < 1 →
      worstMixingTime (MarkovMixing.glauber (probability v h)) (probability v h) ε ≤
        (vectorMixingBound v h ε : ℕ∞)) := by sorry

end IsingVectorBalancing.Subgaussian.Supplement
