-- Prove2me | Theorems.Thm_MultiwayCut_lemma_5_1
-- name    : MultiwayCut.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:00.89625+00:00
-- url     : https://prove2.me/theorems/412d49e7-5c1d-4b7a-98d8-8968aa52b0d5
-- title:
--   Lemma 5.1 — three prefix-sum conditions on a symmetric $A$ make the transformation (5.1) feasible
-- statement:
--   Let $A\in\mathbb R^{k\times k}$ be symmetric and let $f$ be the transformation (5.1), $f_\ell(\mathbf u)=(\mathbf u^\ell)^TA\,\mathbf u^\ell$ for $\ell=1,\dots,k$. Suppose
--   1. $a_{11}=1$ and $a_{ij}\le1$ for every $i,j=1,\dots,k$;
--   2. $\sum_{i=1}^\ell\sum_{j=1}^\ell a_{ij}\ge0$ for every $\ell=1,\dots,k$;
--   3. $\sum_{i=1}^\ell\sum_{j=\ell+1}^r a_{ij}\ge0$ for every $\ell=1,\dots,k$ and $r=\ell+1,\dots,k$.
--
--   Then $f$ is feasible (Definition 3.1): it maps $\Delta_k$ into $[0,1]^k$, fixes every vertex $e_i$, and preserves the order of the coordinates of every $\mathbf u\in\Delta_k$.
--
--   Feasibility is what allows Lemma 2.2 to be applied to $f(\mathbf u),f(\mathbf v)$.
--
--   Differences from the source:
--   - reading: "$f:\Delta_k\to[0,1]^k$ where $f_\ell=\dots$" in the hypothesis → $f$ is the formula (5.1) on $\mathbb R^k$, and $f(\Delta_k)\subseteq[0,1]^k$ is part of the conclusion (`IsFeasibleTransform`); reason: the paper's proof establishes $0\le f_\ell\le1$, and Definition 3.1 requires the codomain
--   - encoding: the paper's coordinates and terminals $1,\dots,k$, $1/\ell$ → `Fin k` from $0$, $1/(\ell+1)$; reason: Lean convention; the same statement after the index shift
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, Lemma 5.1, pp.6–7

import Mathlib
import Definitions.Def_MultiwayCut_Transformation

namespace MultiwayCut

/-- **Lemma 5.1**, Buchbinder, Schwartz & Weizman, *Simplex Transformations and the Multiway Cut
Problem*, manuscript of Nov. 1, 2016, pp.6–7: let `A ∈ ℝ^{k×k}` be symmetric and
`f_ℓ = (u^ℓ)ᵀ A u^ℓ` for every `ℓ = 1, …, k` (the transformation (5.1)). If (1) `a₁₁ = 1` and
`a_ij ≤ 1` for all `i, j`, (2) `Σ_{i=1}^ℓ Σ_{j=1}^ℓ a_ij ≥ 0` for every `ℓ`, and
(3) `Σ_{i=1}^ℓ Σ_{j=ℓ+1}^r a_ij ≥ 0` for every `ℓ` and `r = ℓ + 1, …, k`, then `f` is feasible
(Definition 3.1), including that it maps `Δ_k` into `[0, 1]ᵏ`.

**Formalization Note.** The three conditions are `Lemma51Conditions A` (0-based); `f` is
`quadTransform A`, which sorts, applies (5.1) and puts the values back. The paper's
"`f : Δ_k → [0, 1]ᵏ`" is part of the conclusion: its proof shows `f_k ≥ 0` and `f_1 ≤ 1`. -/
theorem lemma_5_1 {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm)
    (hcond : Lemma51Conditions A) :
    IsFeasibleTransform (quadTransform A) := by sorry

end MultiwayCut
