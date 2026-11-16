-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_linear_transversal_forests
-- name    : FourWayStream.ARHM.Supplement.linear_transversal_forests
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:04:40.294559+00:00
-- url     : https://prove2.me/theorems/005fc021-0bab-44b1-889a-b0e094224acd
-- title:
--   Corollary B.5 — linear transversal forests: $\mathbb P[\tau_{\mathrm{for}}\le(\delta/16)m]\le N^{-\delta m}$
-- statement:
--   Fix $\delta\in(0,1/2)$ and let $c_\delta=\delta/16$. For every even $N\ge2$ and every integer $1\le m\le N^{1/2-\delta}$, independent draws $M_1,\dots,M_m$ from a balanced distribution satisfy
--   $$\mathbb P\big[\tau_{\mathrm{for}}(M_1,\dots,M_m)\le c_\delta m\big]\le N^{-\delta m}.$$
--
--   So every choice of one edge per matching spans a forest with a linear number of edges, except with probability $N^{-\delta m}$; this is the combinatorial input of Theorem 6.7.
--
--   Differences from the source:
--   - encoding: a distribution D on perfect matchings of [N] → a distribution on a finite request type Q, request q naming the perfect matching μ(q); reason: Lean convention; with Q the perfect matchings and μ = id it is the source distribution
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.45, Corollary B.5

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Information
import Definitions.Def_FourWayStream_ARHM_Protocols
import Definitions.Def_FourWayStream_ARHM_Supplement_Simultaneous

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Corollary B.5 (Linear transversal forests), p.45. Fix `δ ∈ (0, 1/2)` and let `c_δ = δ/16`. For
every even `N ≥ 2` and every `1 ≤ m ≤ N^{1/2 − δ}`, independent balanced matchings satisfy
`P[τ_for(M_1, …, M_m) ≤ c_δ m] ≤ N^{−δm}`. -/
theorem linear_transversal_forests (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (N m : ℕ)
    (hN : Even N) (hN2 : 2 ≤ N) (hm : 1 ≤ m) (hmN : (m : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ))
    {Q : Type} [Fintype Q] (μ : Q → Finset (Sym2 (Fin N))) (D : Q → ℝ) (hD : IsBalanced μ D) :
    listProb (m := m) D (fun qs => (tauFor (fun t => μ (qs t)) : ℝ) ≤ δ / 16 * m) ≤
      (N : ℝ) ^ (-(δ * m)) := by sorry

end FourWayStream.ARHM.Supplement
