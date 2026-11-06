-- Prove2me | Theorems.Thm_GeomDRSub_eq_60
-- name    : GeomDRSub.eq_60
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:10:36.596423+00:00
-- url     : https://prove2.me/theorems/859cdff1-4c97-42cf-9ba1-b34882693645
-- title:
--   Eq. (60) — projected ascent bound for every vector sequence
-- statement:
--   Let $K\subseteq\mathbb R^d$ be convex, $D$ a bound on the distances between points of $K$, $\eta>0$, and let $x_1\in K$ and $x_{t+1}=\Pi_K(x_t+\eta\hat g_t)$ for $t=1,\dots,T$, where $\hat g_1,\dots,\hat g_T$ are arbitrary vectors. Then for every $o\in K$,
--   $$
--   \sum_{t=1}^T\langle\hat g_t,\,o-x_t\rangle\le\frac{D^2}{2\eta}+\frac\eta2\sum_{t=1}^T\|\hat g_t\|_2^2 .
--   $$
--   This is the deterministic linear-regret bound of Euclidean projected ascent (Zinkevich) that the online reduction uses.
--
--   Differences from the source:
--   - generalization: K nonempty, compact, convex, down-closed, K ⊆ [0,1]^d → K convex (x₁ ∈ K); reason: the bound uses only convexity and the projection's argmin property; specializes to the standing K
--   - encoding: x_{t+1} = Π_K(x_t + ηĝ_t) → x (t+1) any point with IsEuclideanProj K (x t + η • ĝ t), rounds 0-based; reason: for nonempty closed convex K the projection is the unique such point
--   - encoding: D ≥ diam(K) → ‖a − b‖ ≤ D for all a, b ∈ K; reason: equivalent
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 5.2, p.19, Eq. (60)

import Mathlib
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj

namespace GeomDRSub

/-- **Eq. (60) (projected ascent against every vector sequence).** Aggarwal–Lu, arXiv:2610.00545,
Section 5.2, p.19: "We use Euclidean projected ascent [Zin03], `x_{t+1} = Π_K(x_t + ηĝ_t)` with
`x₁ ∈ K` and step size `η > 0`. Fix `o ∈ K`. … Hence, for every sequence of vectors
`ĝ₁, …, ĝ_T`, `∑_{t=1}^T ⟨ĝ_t, o − x_t⟩ ≤ D²/(2η) + (η/2) ∑_{t=1}^T ‖ĝ_t‖₂²`. (60)"
Here `D ≥ diam(K)` (p.8).

**Formalization Note.** Rounds are 0-based (`x 0` is `x₁`). `Π_K` is the argmin predicate
`OrabonaOL.OGD.IsEuclideanProj`; the statement holds for any convex `K` along any sequence of
projection points (nonemptiness follows from `x 0 ∈ K`), which includes the paper's nonempty
compact convex down-closed `K`. `D` is any bound on the distances between points of `K`. -/
theorem eq_60 {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K)
    (D : ℝ) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D) (η : ℝ) (hη : 0 < η) (T : ℕ)
    (ĝ x : ℕ → EuclideanSpace ℝ (Fin d)) (hx0 : x 0 ∈ K)
    (hupd : ∀ t < T, OrabonaOL.OGD.IsEuclideanProj K (x t + η • ĝ t) (x (t + 1)))
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ K) :
    ∑ t ∈ Finset.range T, inner ℝ (ĝ t) (o - x t) ≤
      D ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖ĝ t‖ ^ 2 := by sorry

end GeomDRSub
