-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_walker_completes
-- name    : FourWayStream.ARHM.Supplement.walker_completes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:11:08.185392+00:00
-- url     : https://prove2.me/theorems/196a53f1-30e7-43e1-bd75-a1a3f27e07a2
-- title:
--   Lemma E.3 — a walker on an $L$-cycle closes with probability at least $\mathbb P[\mathrm{Pois}(R)\ge L]$
-- statement:
--   Let $(n,k)$ be admissible, $G$ an instance of $\mathrm{NGC}_{n,k}$, and $s$ a vertex on a cycle of length $L\ge3$ of $G$. Let $R\ge1$ and let the $R$-repeated stream ($R$ labeled copies of every edge, the algorithm seeing only the edge) be in uniformly random order. Then the walker from $s$ closes with probability at least
--   $$\mathbb P[\mathrm{Pois}(R)\ge L]=1-e^{-R}\sum_{j=0}^{L-1}\frac{R^j}{j!}.$$
--
--   With $L\le2k\le R$ this probability is close to $1$, which gives the classical random-order algorithm of Theorem 7.11.
--
--   Differences from the source:
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.50, Lemma E.3

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC
import Definitions.Def_FourWayStream_ARHM_Supplement_Walker

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Lemma E.3 (A walker on a cycle completes), p.50. Let `(n, k)` be admissible, `E` an instance of
`NGC_{n,k}`, `s` a vertex on a cycle of length `L ≥ 3` of `E`, and `R ≥ 1`. In the `R`-repeated
stream in uniformly random order, the walker from `s` closes with probability at least
`P[Pois(R) ≥ L] = 1 − e^{−R} Σ_{j < L} R^j/j!`. -/
theorem walker_completes (n k : ℕ) (hnk : Admissible n k) (long : Bool)
    (E : Finset (Sym2 (Fin n))) (hE : IsNGC n k long E) (L : ℕ) (cyc : ZMod L → Fin n)
    (hcyc : IsCycleOf E L cyc) (R : ℕ) (hR : 1 ≤ R) :
    1 - poissonLT R L ≤
      avgRepRandOrder E R (fun str => if (walk (cyc 0) (List.ofFn str)).closed = true then 1 else 0) := by sorry

end FourWayStream.ARHM.Supplement
