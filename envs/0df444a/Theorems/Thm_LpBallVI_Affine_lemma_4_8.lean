-- Prove2me | Theorems.Thm_LpBallVI_Affine_lemma_4_8
-- name    : LpBallVI.Affine.lemma_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:12:45.908682+00:00
-- url     : https://prove2.me/theorems/5c61ea31-1e26-4c5f-b1ac-24e435de0b07
-- title:
--   Lemma 4.8 — every auxiliary coordinate ζ*_ℓ is within 2‖z* − s‖_p of σ_λ(h_ℓ(ζ*))
-- statement:
--   Let $1 < p < \infty$, $p \ne 2$, a well-formed PureCircuit instance with $n \ge 2$ nodes, a coefficient family, $R > 0$, $c_R > 0$, and $F$ the affine operator (39)–(40). For $z^* = (z^*_0, \zeta^*) \in B_p(R)$ let $s = S_R(F(z^*))$ and $\lambda = \|F(z^*)\|_q / R^{p-1}$ (so that $F(z^*) = \lambda J_p(s)$, (42)). Then for every auxiliary coordinate $\ell$,
--   $$|\zeta^*_\ell - \sigma_\lambda(h_\ell(\zeta^*))| \le 2\|z^* - s\|_p.$$
--   The distance to the support point controls how far the inverse-mapping equations (38) fail.
--
--   Differences from the source:
--   - generalization: the coefficients of Lemma 4.6 for ϕ̂_NOR, ϕ̂_PURIFY (rational, η = 1/128), the integer radius R and c_R of Lemma 4.10 → any real coefficient family, any real R > 0, any c_R > 0; reason: the proof uses only (37)–(42) and Lemma 4.7; the paper's choice is one instance
--   - generalization: z* an ϵ_R-approximate VI solution (41) → any z* ∈ B_p(R); reason: the proof does not use (41); approximate solutions are points of the ball
--   - reading: λ, the unique λ > 0 with F(z*) = λ J_p(s) (42) → λ = ‖F(z*)‖_q / R^{p−1}; reason: the formula Lemma 4.10 names; by (5), J_p(S_R(F)) = R^{p−1} F / ‖F‖_q, so this is that λ
--   - encoding: coordinates z = (z_0, ζ) ∈ ℝ^{d_aux+1} → functions on Option (Fin n × Fin m × Fin 6), none = z_0; reason: relabelling of the 6mn + 1 coordinates
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 32, Lemma 4.8, (41)–(43)

import Mathlib
import Definitions.Def_LpBallVI_Affine_Construction

namespace LpBallVI.Affine

/-- **Lemma 4.8**, p. 32: for the affine operator `F` of (39)–(40) on `B_p^{d_aux+1}(R)`, a point
`z*` of the ball, its support point `s = S_R(F(z*))` and the multiplier `λ = ‖F(z*)‖_q / R^{p−1}`
(the `λ > 0` with `F(z*) = λ J_p(s)`, (42)), every auxiliary coordinate satisfies
`|ζ*_ℓ − σ_λ(h_ℓ(ζ*))| ≤ 2‖z* − s‖_p`. Stated for every coefficient family, radius `R > 0` and
`c_R > 0`. -/
theorem lemma_4_8 (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) (I : PCInst) (hI : I.WellFormed)
    (hn : 2 ≤ I.n) (c : CoeffFamily) (R cR : ℝ) (hR : 0 < R) (hcR : 0 < cR)
    (z : Coord I.n c.m → ℝ) (hz : z ∈ ball p R) :
    let F := vecF p I c cR
    let s := supportPt p R (F z)
    let lam := lpNorm (dualExp p) (F z) / R ^ (p - 1)
    ∀ ℓ : Fin I.n × Fin c.m × Fin 6,
      |z (some ℓ) - sigmaLam p lam (auxInput p I c z ℓ)| ≤ 2 * lpNorm p (z - s) := by sorry

end LpBallVI.Affine
