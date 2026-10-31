-- Prove2me | Theorems.Thm_MultiwayCut_lemma_2_1
-- name    : MultiwayCut.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:13.37841+00:00
-- url     : https://prove2.me/theorems/f148ec49-6d29-4d11-819d-0b6e13de243f
-- title:
--   Lemma 2.1 — exponential clocks separate $u$ and $u+\varepsilon(e_i-e_j)$ with probability at most $\varepsilon(2-u_i-u_j)$
-- statement:
--   Let $\mathbf u,\mathbf v\in\Delta_k$ differ only in two coordinates $i\ne j$, with $v_i=u_i+\varepsilon$ and $v_j=u_j-\varepsilon$ for some $\varepsilon\ge0$. Then the probability that the exponential clocks algorithm assigns $\mathbf u$ and $\mathbf v$ to different terminals satisfies
--   $$\Pr[\text{$\mathbf u$ and $\mathbf v$ separated}]\le\varepsilon\,(2-u_i-u_j).$$
--
--   The paper quotes this bound from Buchbinder, Naor and Schwartz; it gives the exponential-clocks part $\beta_{i,j}\le 2-u_i-u_j$ of the cut density of Algorithm 3, and it holds at every $\varepsilon$, not only in the limit.
--
--   Differences from the source:
--   - encoding: the paper's coordinates and terminals $1,\dots,k$, $1/\ell$ → `Fin k` from $0$, $1/(\ell+1)$; reason: Lean convention; the same statement after the index shift
--   - encoding: probability over i.i.d. $Z_i\sim\exp(1)$; $\arg\min Z_i/u_i$ → measure of the event under the product of `expMeasure 1` (outer measure); the argmin is taken over $\{i: u_i>0\}$ by cross-multiplication, ties to the least index; reason: $Z_i/0=+\infty$ in the paper, while Lean's $x/0=0$ would let a zero coordinate win; ties have probability $0$
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, Lemma 2.1, p.3

import Mathlib
import Definitions.Def_MultiwayCut_ExpClocks
import Definitions.Def_MultiwayCut_CutDensity

namespace MultiwayCut

/-- **Lemma 2.1** (exponential clocks), Buchbinder, Schwartz & Weizman, *Simplex
Transformations and the Multiway Cut Problem*, manuscript of Nov. 1, 2016, p.3 (cited there
from [5]): given `u, v ∈ Δ_k` that differ only in coordinates `i` and `j`, where
`vᵢ = uᵢ + ε` and `v_j = u_j − ε` for some `ε ≥ 0`, the probability that `u` and `v` are
assigned to different terminals by the exponential clocks algorithm is at most
`ε (2 − uᵢ − u_j)`.

**Formalization Note.** Coordinates are `Fin k`, 0-based; `v = u + ε(eᵢ − e_j)` is
`ijShift u i j ε`; `i ≠ j` because the two coordinates are distinct. -/
theorem lemma_2_1 {k : ℕ} [NeZero k] (u v : Fin k → ℝ) (hu : u ∈ stdSimplex ℝ (Fin k))
    (hv : v ∈ stdSimplex ℝ (Fin k)) (i j : Fin k) (hij : i ≠ j) (ε : ℝ) (hε : 0 ≤ ε)
    (huv : v = ijShift u i j ε) :
    sepExp u v ≤ ε * (2 - u i - u j) := by sorry

end MultiwayCut
