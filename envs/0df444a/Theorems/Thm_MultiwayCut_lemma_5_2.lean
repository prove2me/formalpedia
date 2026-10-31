-- Prove2me | Theorems.Thm_MultiwayCut_lemma_5_2
-- name    : MultiwayCut.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:57.936007+00:00
-- url     : https://prove2.me/theorems/9f9bcc17-9774-40e9-b740-4b7d1d92ab49
-- title:
--   Lemma 5.2 — the CKR cut density after the transformation (5.1) is at most the sum (5.2)
-- statement:
--   Let $A\in\mathbb R^{k\times k}$ be symmetric and satisfy the conditions of Lemma 5.1, let $f$ be the transformation (5.1), and write $\mathbf a_\ell$ for the $\ell$-th row (equivalently column) of $A$. Let $u_1\ge\dots\ge u_k$ and $1\le i<j\le k$. Then the cut density $\alpha_{i,j}$ at $\mathbf u$ of CKR executed on $f(\mathbf u),f(\mathbf v)$ satisfies
--   $$\alpha_{i,j}\le\sum_{\ell=1}^{i-1}\frac2\ell\bigl|(\mathbf a_i-\mathbf a_j)\cdot\mathbf u^\ell\bigr|+\frac2i\Bigl|\Bigl(\sum_{\ell=1}^{i}\mathbf a_\ell-\mathbf a_j\Bigr)\cdot\mathbf u^i\Bigr|+\sum_{\ell=i+1}^{j-1}\frac2\ell\bigl|\mathbf a_j\cdot\mathbf u^\ell\bigr|+\frac2j\Bigl|\Bigl(\sum_{\ell=1}^{j}\mathbf a_\ell\Bigr)\cdot\mathbf u^j\Bigr| .\tag{5.2}$$
--
--   It reduces the CKR cut density to linear functionals of the flattened vectors $\mathbf u^\ell$, whose signs Observation 5.1 and Lemma 5.3 then control.
--
--   Differences from the source:
--   - encoding: the paper's coordinates and terminals $1,\dots,k$, $1/\ell$ → `Fin k` from $0$, $1/(\ell+1)$; reason: Lean convention; the same statement after the index shift
--   - reading: edges of type $(i,j)$ with $u_1\ge\dots\ge u_k$ (the paper's standing "without loss of generality", pp.5–6) → the $(i,j)$-edge in the identity order, $u$ non-increasing in `Fin k`; reason: exactly the paper's normalization; other orders follow by renaming coordinates
--   - encoding: $\limsup_{\varepsilon\to0}\Pr[g(u)\ne g(v)]/\varepsilon\le\gamma$ → for every $\eta>0$, eventually as $\varepsilon\to0^+$, the ratio is at most $\gamma+\eta$, for those $\varepsilon$ at which $(u,v)$ is an $(i,j)$-edge; reason: the same condition; an edge has $\varepsilon\ge0$, and `Filter.limsup` in $\mathbb R$ returns a junk value on unbounded functions
--   - reading: "the conditions of Lemma 5.1" → symmetry of $A$ and `Lemma51Conditions A`; reason: Lemma 5.1's first sentence makes $A$ symmetric
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, Lemma 5.2, (5.2), p.7

import Mathlib
import Definitions.Def_MultiwayCut_CKR
import Definitions.Def_MultiwayCut_CutDensity
import Definitions.Def_MultiwayCut_Transformation

open Matrix

namespace MultiwayCut

/-- **Lemma 5.2**, Buchbinder, Schwartz & Weizman, *Simplex Transformations and the Multiway
Cut Problem*, manuscript of Nov. 1, 2016, p.7: if `A ∈ ℝ^{k×k}` satisfies the conditions of
Lemma 5.1, then the cut density `α_{i,j}` of Algorithm 2 executed after the transformation `f`
of (5.1) satisfies, at a sorted `u` (`u₁ ≥ … ≥ u_k`), (5.2):
`α_{i,j} ≤ Σ_{ℓ=1}^{i−1} (2/ℓ) |(aᵢ − a_j)·u^ℓ| + (2/i) |(Σ_{ℓ=1}^{i} a_ℓ − a_j)·u^i|
 + Σ_{ℓ=i+1}^{j−1} (2/ℓ) |a_j·u^ℓ| + (2/j) |(Σ_{ℓ=1}^{j} a_ℓ)·u^j|`,
where `a_ℓ` is the `ℓ`-th row (equivalently column) of `A`.

**Formalization Note.** 0-based: positions `i < j : Fin k`, `1/ℓ` becomes `1/(ℓ + 1)`,
`u^ℓ` is `flat u (ℓ − 1)`, the row `a_ℓ` is `A (ℓ − 1)`. The coordinates of `u` are already
sorted (the paper's standing "without loss of generality", p.5–6), so the order of the
`(i, j)`-edge is the identity. The cut density is `IJDensityLE` (Definition 2.1) of the
separation probability `Pr_CKR[f(u), f(v) separated]`; symmetry of `A` is part of "the
conditions of Lemma 5.1" (its first sentence). -/
theorem lemma_5_2 {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm)
    (hcond : Lemma51Conditions A) (u : Fin k → ℝ) (i j : Fin k) :
    IJDensityLE (fun x y => sepCKR (quadTransform A x) (quadTransform A y))
      (Equiv.refl (Fin k)) i j u
      (∑ l ∈ Finset.Iio i, 2 / ((l.val : ℝ) + 1) * |(A i - A j) ⬝ᵥ flat u l| +
        2 / ((i.val : ℝ) + 1) * |((∑ l ∈ Finset.Iic i, A l) - A j) ⬝ᵥ flat u i| +
        ∑ l ∈ Finset.Ioo i j, 2 / ((l.val : ℝ) + 1) * |A j ⬝ᵥ flat u l| +
        2 / ((j.val : ℝ) + 1) * |(∑ l ∈ Finset.Iic j, A l) ⬝ᵥ flat u j|) := by sorry

end MultiwayCut
