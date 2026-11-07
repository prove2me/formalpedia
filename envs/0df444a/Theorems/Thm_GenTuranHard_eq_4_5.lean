-- Prove2me | Theorems.Thm_GenTuranHard_eq_4_5
-- name    : GenTuranHard.eq_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:46.275836+00:00
-- url     : https://prove2.me/theorems/5179fc57-8bdf-499c-abe6-0357dee003d4
-- title:
--   Inequality (4.5) — $v(Z) = Bn\prod_i (n^{d_i}+1) \le 2^s B n^{1+\sum_i d_i}$
-- statement:
--   Let $G$ be a graph on $n$ vertices, $t = v(T)$, $s = t - 2$, $\mathbf x$ as in (4.3) and $Z = L_{\mathbf x}(G)(B)$. Then
--
--   $$
--   v(Z) = v(L_{\mathbf x}(G))\,B = \Big(v(G) \prod_{i=1}^{s} (x_i + 1)\Big) B = B n \prod_{i=1}^{s} (n^{d_i} + 1) \le 2^s B n^{1 + \sum_{i=1}^{s} d_i}.
--   $$
--
--   The bound shows that $Z$ has polynomially many vertices and controls the error terms of (2.1).
--
--   **Formalization Note** The statement is for every $t$, every $n$ (both sides vanish at $n = 0$) and every $B$.
--
--   Differences from the source:
--   - generalization: the §4 setting (n ≥ 1, B a positive integer, v(T) ≥ 3) → every t, n and B; reason: the identity and the bound hold for all values; the source's case is included
--   - encoding: Z = L_x(G)(B), its clusters C_v → Zgraph x G B on Fin (v(L_x(G))·B), vertex i in the cluster of vertex i / B; reason: one numbering of the B-blow-up; every quantity involved is isomorphism-invariant
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), (4.5), p.17

import Mathlib
import Definitions.Def_GenTuranHard_A0
import Definitions.Def_GenTuranHard_Zgraph

set_option autoImplicit false

namespace GenTuranHard

/-- **Inequality (4.5)** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, (4.5), p.17). For
`Z = L_x(G)(B)` with `x` as in (4.3), `n = v(G)`, `t = v(T)` and `s = t − 2`,
`v(Z) = v(L_x(G))·B = (v(G)·∏_{i=1}^s (x_i + 1))·B = B·n·∏_{i=1}^s (n^{d_i} + 1) ≤ 2^s B n^{1 + Σ_i d_i}`.

**Formalization Note** Stated for every `t` and every `n` (for `n = 0` both sides are `0`); `d` is
`dList t (t − 2)` and `x = xVec t n`. -/
theorem eq_4_5 (t : ℕ) (G : FinGraph) (B : ℕ) :
    (Zgraph (xVec t G.1) G B).1 = G.1 * ((xVec t G.1).map (· + 1)).prod * B ∧
      G.1 * ((xVec t G.1).map (· + 1)).prod * B =
        B * G.1 * ((dList t (t - 2)).map (fun d => G.1 ^ d + 1)).prod ∧
      B * G.1 * ((dList t (t - 2)).map (fun d => G.1 ^ d + 1)).prod ≤
        2 ^ (t - 2) * B * G.1 ^ (1 + (dList t (t - 2)).sum) := by sorry

end GenTuranHard
