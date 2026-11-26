-- Prove2me | Theorems.Thm_LefebvreVariations_minkowski_hlawka_unimodular_ball
-- name    : LefebvreVariations.minkowski_hlawka_unimodular_ball
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:23:55.281244+00:00
-- url     : https://prove2.me/theorems/ec5bfefc-8d35-47ec-a1a9-dc4ea0fd5ade
-- title:
--   Lefebvre's variations: Hlawka's theorem, a unimodular lattice avoiding a ball of volume below 2ζ(d)
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   This is the Minkowski–Hlawka theorem in its geometry-of-numbers form, for a Euclidean ball.
--
--   Let $d \ge 2$, let $\zeta(d) = \sum_{n \ge 1} n^{-d}$, and let $\rho > 0$ be such that the ball $B(0,\rho) \subset \mathbb{R}^d$ has volume $\operatorname{vol} B(0,\rho) < 2\,\zeta(d)$. Then there is a lattice $\Lambda \subset \mathbb{R}^d$ of covolume $1$ that has no nonzero point in the open ball: $\|v\| \ge \rho$ for every $v \in \Lambda \setminus \{0\}$.
--
--   In terms of a basis: there are $b_1,\dots,b_d \in \mathbb{R}^d$ with $|\det(b_1,\dots,b_d)| = 1$ and $\bigl\|\sum_i z_i b_i\bigr\| \ge \rho$ for every nonzero $z \in \mathbb{Z}^d$.
--
--   Hlawka (1943) proved this by averaging over the unimodular lattices (Siegel's mean value theorem): the average number of primitive lattice points in a bounded measurable set $S$ is $\operatorname{vol}(S)/\zeta(d)$; primitive points come in pairs $\pm v$, so if $\operatorname{vol}(S) < 2\zeta(d)$ some lattice has none, hence none at all when $S$ is a ball.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin d)`. The lattice is given by a basis `b : Module.Basis (Fin d) ℝ _` of $\mathbb{R}^d$ (so it spans), its covolume is `|det|` of the basis in the standard orthonormal basis, and the lattice points are `∑ i, z i • b i` with `z : Fin d → ℤ`. The volume is `MeasureTheory.volume.real` of `Metric.ball 0 ρ`, and `ζ(d)` is written as the `tsum` `∑' n, 1/(n+1)^d`, exactly as in the platform theorem `SpherePackingBeyond.minkowski_hlawka` (for `d ≥ 2` the series is summable; for `d = 1` it would be junk, which is why `2 ≤ d` is assumed). The hypothesis is strict, which is what the averaging argument gives; the packing statement follows by letting $\rho$ increase to the radius with $\operatorname{vol} B(0,\rho) = 2\zeta(d)$.
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `SpherePackingBeyond.minkowski_hlawka` ($\Delta^L_d \ge \zeta(d)/2^{d-1}$, Hlawka 1943). The reduction proves in Lean that a lattice packing with minimal distance at least $2$ has density $\operatorname{vol}B(0,1)/\mathrm{covol}$, rescales the lattice of this statement by $2/\rho$ (density $\operatorname{vol}B(0,\rho)/2^d$), and lets $\rho$ increase to the radius with volume $2\zeta(d)$. This statement is the analytic core (Siegel's mean value theorem) of the base statement, written without any packing definition; it is not a special case of the base statement, and it is slightly stronger than it (one lattice for each $\rho$ instead of a supremum).
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). E. Hlawka, Zur Geometrie der Zahlen, Math. Z. 49 (1943), 285–312 (the Minkowski–Hlawka theorem). C. L. Siegel, A mean value theorem in geometry of numbers, Ann. of Math. 46 (1945), 340–347. C. A. Rogers, The number of lattice points in a set, Proc. London Math. Soc. 6 (1956), 305–320. J. W. S. Cassels, An Introduction to the Geometry of Numbers, Ch. V, Thm. 2 (Corollary on lattices with no point in a star body of volume < 2ζ(d)). H. Cohn, A conceptual breakthrough in sphere packing, Notices AMS 64 (2017), §3. Origin of this statement: it is the missing step of a reduction of SpherePackingBeyond.minkowski_hlawka (Δᴸ_d ≥ ζ(d)/2^{d-1}). In that reduction everything else is proved in Lean: a lattice packing of Def_TenChallenges_SpherePacking with minimal distance ≥ 2 has upper density vol B(0,1)/covolume (via Mathlib's lattice-point count N(r)/r^d → vol/covol), the scaling of a basis by 2/ρ, and the limit ρ ↗ ρ₀ with vol B(0,ρ₀) = 2ζ(d).

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace LefebvreVariations
theorem minkowski_hlawka_unimodular_ball (d : ℕ) (hd : 2 ≤ d) (ρ : ℝ) (hρ : 0 < ρ)
    (hvol : MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ) <
      2 * ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℝ) ^ d)) :
    ∃ b : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
      |(EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det b| = 1 ∧
      ∀ z : Fin d → ℤ, z ≠ 0 → ρ ≤ ‖∑ i, z i • b i‖ := by sorry
end LefebvreVariations
