-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_transversal_forest_tail
-- name    : FourWayStream.ARHM.Supplement.transversal_forest_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:04:13.019273+00:00
-- url     : https://prove2.me/theorems/b15722cb-24be-477c-a031-dcd16bc3cbc4
-- title:
--   Proposition B.3 — transversal-forest tail $\mathbb P[\tau_{\mathrm{for}}\le s]\le T_{N,m}(s)$
-- statement:
--   Let $N\ge2$ be even and $m\ge1$. For independent draws $M_1,\dots,M_m$ from a balanced distribution on perfect matchings of $[N]$ (every pair lies in the matching with probability $1/(N-1)$) and every integer $1\le s\le N/2$,
--   $$\mathbb P\big[\tau_{\mathrm{for}}(M_1,\dots,M_m)\le s\big]\le T_{N,m}(s)=\binom N{2s}\left(\frac{\binom{2s}2}{N-1}\right)^m.$$
--
--   It is the tail estimate behind Corollary B.5.
--
--   **Formalization Note** The probability is a sum over request lists weighted by $\prod_tD(q_t)$.
--
--   Differences from the source:
--   - encoding: a distribution D on perfect matchings of [N] → a distribution on a finite request type Q, request q naming the perfect matching μ(q); reason: Lean convention; with Q the perfect matchings and μ = id it is the source distribution
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.44, Proposition B.3 and the definition of T_{N,m}(s)

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

/-- Proposition B.3 (Transversal-forest tail), p.44. For `N ≥ 2` even, `m ≥ 1`, independent draws
`M_1, …, M_m` from a balanced distribution and every integer `1 ≤ s ≤ N/2`,
`P[τ_for(M_1, …, M_m) ≤ s] ≤ T_{N,m}(s) = binom(N, 2s) (binom(2s, 2)/(N − 1))^m`. -/
theorem transversal_forest_tail (N m : ℕ) (hN : Even N) (hN2 : 2 ≤ N) (hm : 1 ≤ m)
    {Q : Type} [Fintype Q] (μ : Q → Finset (Sym2 (Fin N))) (D : Q → ℝ) (hD : IsBalanced μ D)
    (s : ℕ) (hs : 1 ≤ s) (hsN : 2 * s ≤ N) :
    listProb (m := m) D (fun qs => tauFor (fun t => μ (qs t)) ≤ s) ≤ tailT N m s := by sorry

end FourWayStream.ARHM.Supplement
