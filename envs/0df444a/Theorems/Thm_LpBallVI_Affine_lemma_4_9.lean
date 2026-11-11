-- Prove2me | Theorems.Thm_LpBallVI_Affine_lemma_4_9
-- name    : LpBallVI.Affine.lemma_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:12:47.241769+00:00
-- url     : https://prove2.me/theorems/cb807732-7ce2-4ed7-8c84-96dc08664319
-- title:
--   Lemma 4.9 — every node value x_v is within 12H‖z* − s‖_p of N^v_λ(s_v(x))
-- statement:
--   In the setting of Lemma 4.8 (same $p$, instance, coefficient family, $R$, $c_R$, $z^*$, $s$ and $\lambda$), let $x_v$ be the node values (37), $N^v_\lambda$ the weighted approximation function of the gate type of $v$, and $H = \sum_j |\alpha_{{\rm NOR},j}| + \sum_j |\alpha_{{\rm PURIFY},j}|$. Then for every node $v$
--   $$|x_v - N^v_\lambda(s_v(x))| \le 12 H \|z^* - s\|_p.$$
--   Node values of an approximate solution thus follow the gate functions up to an error controlled by the VI accuracy.
--
--   Differences from the source:
--   - generalization: the coefficients of Lemma 4.6 for ϕ̂_NOR, ϕ̂_PURIFY (rational, η = 1/128), the integer radius R and c_R of Lemma 4.10 → any real coefficient family, any real R > 0, any c_R > 0; reason: the proof uses only (37)–(42) and Lemma 4.7; the paper's choice is one instance
--   - generalization: z* an ϵ_R-approximate VI solution (41) → any z* ∈ B_p(R); reason: the proof does not use (41); approximate solutions are points of the ball
--   - reading: λ, the unique λ > 0 with F(z*) = λ J_p(s) (42) → λ = ‖F(z*)‖_q / R^{p−1}; reason: the formula Lemma 4.10 names; by (5), J_p(S_R(F)) = R^{p−1} F / ‖F‖_q, so this is that λ
--   - encoding: coordinates z = (z_0, ζ) ∈ ℝ^{d_aux+1} → functions on Option (Fin n × Fin m × Fin 6), none = z_0; reason: relabelling of the 6mn + 1 coordinates
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 32, Lemma 4.9, (45), (46)

import Mathlib
import Definitions.Def_LpBallVI_Affine_Construction

namespace LpBallVI.Affine

/-- **Lemma 4.9**, p. 32: in the setting of Lemma 4.8, every node value `x_v` of (37) satisfies
`|x_v − N^v_λ(s_v(x))| ≤ 12 H ‖z* − s‖_p`, where `N^v_λ` is the weighted approximation function of
the gate type of `v` and `H = ∑_j |α_{NOR,j}| + ∑_j |α_{PURIFY,j}|` (45). -/
theorem lemma_4_9 (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) (I : PCInst) (hI : I.WellFormed)
    (hn : 2 ≤ I.n) (c : CoeffFamily) (R cR : ℝ) (hR : 0 < R) (hcR : 0 < cR)
    (z : Coord I.n c.m → ℝ) (hz : z ∈ ball p R) :
    let F := vecF p I c cR
    let s := supportPt p R (F z)
    let lam := lpNorm (dualExp p) (F z) / R ^ (p - 1)
    ∀ v : Fin I.n,
      |nodeValue p I c z v -
          weightedApprox p lam (coeffsOf I c v).1 (coeffsOf I c v).2.1 (coeffsOf I c v).2.2
            (I.sIn (nodeValue p I c z) v)| ≤ 12 * c.H * lpNorm p (z - s) := by sorry

end LpBallVI.Affine
