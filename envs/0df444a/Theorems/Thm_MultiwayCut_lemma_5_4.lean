-- Prove2me | Theorems.Thm_MultiwayCut_lemma_5_4
-- name    : MultiwayCut.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:46.478393+00:00
-- url     : https://prove2.me/theorems/b836dbcc-7242-4287-bd91-52e0749c6255
-- title:
--   Lemma 5.4 — CKR after the matrix (5.3) has cut density $\alpha_{i,j}\le\frac{44}{27}(u_i+u_j)+\frac{55}{108}\sum_{\ell\ne i,j}u_\ell$
-- statement:
--   Let $f$ be the transformation (5.1) with the matrix $A$ of (5.3). For every $k\ge1$, every $\mathbf u$ with $u_1\ge\dots\ge u_k$ and every $1\le i<j\le k$, the cut density at $\mathbf u$ of CKR executed on $f(\mathbf u),f(\mathbf v)$, for edges of type $(i,j)$, satisfies
--   $$\alpha_{i,j}\le\frac{44}{27}(u_i+u_j)+\frac{55}{108}\sum_{\ell\ne i,j}u_\ell .$$
--
--   Combined with Lemma 2.1 and $p=121/229$ it yields the overall density $297/229$ of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: the paper's coordinates and terminals $1,\dots,k$, $1/\ell$ → `Fin k` from $0$, $1/(\ell+1)$; reason: Lean convention; the same statement after the index shift
--   - reading: edges of type $(i,j)$ with $u_1\ge\dots\ge u_k$ (the paper's standing "without loss of generality", pp.5–6) → the $(i,j)$-edge in the identity order, $u$ non-increasing in `Fin k`; reason: exactly the paper's normalization; other orders follow by renaming coordinates
--   - encoding: $\limsup_{\varepsilon\to0}\Pr[g(u)\ne g(v)]/\varepsilon\le\gamma$ → for every $\eta>0$, eventually as $\varepsilon\to0^+$, the ratio is at most $\gamma+\eta$, for those $\varepsilon$ at which $(u,v)$ is an $(i,j)$-edge; reason: the same condition; an edge has $\varepsilon\ge0$, and `Filter.limsup` in $\mathbb R$ returns a junk value on unbounded functions
--   - reading: the matrix (5.3) printed with "…" for a general $k$ → `A53 k` for every $k\ge1$, defined by the entry formula (the top-left $k\times k$ block of the printed pattern); reason: the paper never restricts $k$; this is the only matrix consistent with the printed pattern
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, Lemma 5.4, p.8 (proof pp.8–11)

import Mathlib
import Definitions.Def_MultiwayCut_CKR
import Definitions.Def_MultiwayCut_CutDensity
import Definitions.Def_MultiwayCut_Transformation
import Definitions.Def_MultiwayCut_A53

namespace MultiwayCut

/-- **Lemma 5.4**, Buchbinder, Schwartz & Weizman, *Simplex Transformations and the Multiway
Cut Problem*, manuscript of Nov. 1, 2016, p.8: the cut density of Algorithm 2 executed after
applying the transformation defined by the matrix (5.3) satisfies
`α_{i,j} ≤ 44/27 (uᵢ + u_j) + 55/108 Σ_{ℓ≠i,j} u_ℓ`.

**Formalization Note.** For every `k ≥ 1`, at a sorted `u` (the paper's standing "without loss
of generality"; the `(i, j)`-edge's order is the identity), positions `i < j : Fin k` 0-based.
The cut density is `IJDensityLE` (Definition 2.1) of `Pr_CKR[f(u), f(v) separated]` with
`f = quadTransform (A53 k)`. -/
theorem lemma_5_4 {k : ℕ} [NeZero k] (u : Fin k → ℝ) (i j : Fin k) :
    IJDensityLE (fun x y => sepCKR (quadTransform (A53 k) x) (quadTransform (A53 k) y))
      (Equiv.refl (Fin k)) i j u
      (44 / 27 * (u i + u j) + 55 / 108 * ∑ ℓ ∈ Finset.univ \ {i, j}, u ℓ) := by sorry

end MultiwayCut
