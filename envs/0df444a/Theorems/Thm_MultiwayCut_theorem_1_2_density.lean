-- Prove2me | Theorems.Thm_MultiwayCut_theorem_1_2_density
-- name    : MultiwayCut.theorem_1_2_density
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:22.754735+00:00
-- url     : https://prove2.me/theorems/954c525b-49b1-4412-87df-8e614e037a85
-- title:
--   Proof of Theorem 1.2 — Algorithm 3 with $p=121/229$ and (5.3) separates every $(i,j)$-edge with probability $\le\frac{297}{229}\varepsilon+C\varepsilon^2$ (finite-$\varepsilon$ form)
-- statement:
--   Run Algorithm 3 with $p=\frac{121}{229}$ and the transformation (5.1) defined by the matrix (5.3). The paper shows (p.8) that for edges of type $(i,j)$
--   $$(1-p)\alpha_{i,j}+p\beta_{i,j}\le2p+(1-p)\tfrac{55}{108}\sum_{\ell\ne i,j}u_\ell+(u_i+u_j)\bigl((1-p)\tfrac{44}{27}-p\bigr)=\tfrac{242}{229}+\tfrac{55}{229}\sum_{\ell=1}^ku_\ell=\tfrac{297}{229}.$$
--
--   Stated in the form the corrected reduction needs: for every $k\ge1$ there is a constant $C$ such that for every $(i,j)$-edge $(\mathbf u,\mathbf v)$ with parameter $\varepsilon$ (in any order of the coordinates, any $i<j$), the probability that Algorithm 3 assigns $\mathbf u$ and $\mathbf v$ to different terminals is at most
--   $$\frac{297}{229}\,\varepsilon+C\varepsilon^2 .$$
--   In particular the cut density of Algorithm 3 is at most $297/229$ for every type $(i,j)$.
--
--   Differences from the source:
--   - generalization: $(1-p)\alpha_{i,j}+p\beta_{i,j}\le\frac{297}{229}$ for the $\limsup$ cut density → $\mathrm{sep}_3(u,v)\le\frac{297}{229}\varepsilon+C\varepsilon^2$ on every $(i,j)$-edge, with $C$ depending only on $k$; reason: the printed $\limsup$ bound is true, and the finite-$\varepsilon$ form implies it (divide by $\varepsilon$ and let $\varepsilon\to0^+$); the stronger form is the one the corrected reduction (`karger_reduction`) consumes, since the $\limsup$ bound alone does not imply the approximation ratio
--   - encoding: edges of type $(i,j)$ after sorting the coordinates → an $(i,j)$-edge in an arbitrary order `π`; reason: the paper's "there exists an order of the coordinates", p.4
--   - encoding: the paper's coordinates and terminals $1,\dots,k$, $1/\ell$ → `Fin k` from $0$, $1/(\ell+1)$; reason: Lean convention; the same statement after the index shift
--   - reading: the matrix (5.3) printed with "…" for a general $k$ → `A53 k` for every $k\ge1$, defined by the entry formula (the top-left $k\times k$ block of the printed pattern); reason: the paper never restricts $k$; this is the only matrix consistent with the printed pattern
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, proof of Theorem 1.2, p.8

import Mathlib
import Definitions.Def_MultiwayCut_Algorithm3
import Definitions.Def_MultiwayCut_CutDensity
import Definitions.Def_MultiwayCut_Transformation
import Definitions.Def_MultiwayCut_A53

namespace MultiwayCut

/-- **Cut density of the 297/229 algorithm** (finite-`ε` form), Buchbinder, Schwartz
& Weizman, *Simplex Transformations and the Multiway Cut Problem*, manuscript of Nov. 1, 2016,
proof of Theorem 1.2, p.8: Algorithm 3 with `p = 121/229` and the transformation defined by the
matrix (5.3) has, for edges of type `(i, j)`,
`(1 − p) α_{i,j} + p β_{i,j} ≤ 2p + (1 − p)(55/108) Σ_{ℓ≠i,j} u_ℓ + (uᵢ + u_j)((1 − p)(44/27) − p)
 = 242/229 + (55/229) Σ_{ℓ=1}^k u_ℓ = 297/229`.

Posed in the form the corrected reduction (`karger_reduction`) consumes: for every `k ≥ 1` there
is a constant `C` such that on every `(i, j)`-edge `(u, v)` (any order `π`, any `i < j`) with
parameter `ε`, the separation probability of Algorithm 3 is at most `297/229 · ε + C ε²`. This
implies the printed lim sup bound `≤ 297/229`.

**Formalization Note.** `C` may depend on `k` but not on the edge. -/
theorem theorem_1_2_density {k : ℕ} [NeZero k] :
    ∃ C : ℝ, ∀ (π : Equiv.Perm (Fin k)) (i j : Fin k) (ε : ℝ) (u v : Fin k → ℝ),
      IsIJEdge π i j ε u v →
        alg3Sep (121 / 229) (quadTransform (A53 k)) u v ≤ 297 / 229 * ε + C * ε ^ 2 := by sorry

end MultiwayCut
