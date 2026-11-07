-- Prove2me | Theorems.Thm_IntQuotHNP_lemma_2_6
-- name    : IntQuotHNP.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:01.673226+00:00
-- url     : https://prove2.me/theorems/472f1c8e-0457-4c11-a86f-e5674a843a87
-- title:
--   Lemma 2.6 — paired length bound $\|b_j\|_2\|b_j^\vee\|_2\le4^m$ for an LLL-reduced basis
-- statement:
--   Let $b_1,\dots,b_m\in\mathbb R^d$ be linearly independent and LLL-reduced with parameter $\delta=3/4$, and let $b_1^\vee,\dots,b_m^\vee$ be the dual basis: the vectors in the real span of the $b_i$ with $\langle b_i,b_j^\vee\rangle=\delta_{ij}$. Then for every $j$,
--   $$
--   \|b_j\|_2\,\|b_j^\vee\|_2\le4^m .
--   $$
--   This bound relates each reduced basis vector to its dual partner, and it turns the dual quantity $\lambda_{\mathrm{target}}$ into a bound on basis lengths in (2).
--
--   Differences from the source:
--   - encoding: the dual basis as an object of Definition 2.5 → any family in the span satisfying the defining equations; reason: these equations determine the family uniquely, so no instance changes
--   - encoding: 1 ≤ m ≤ d → m and d free natural numbers; reason: m ≤ d follows from linear independence, and m = 0 is vacuous
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Lemma 2.6, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_IntQuotHNP_LLLReduced

open InnerProductSpace

namespace IntQuotHNP

/-- **Lemma 2.6 (paired length bound via the dual lattice).**
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), Lemma 2.6, p.15 (PDF p.16): "Let b₁, . . . , b_m be an LLL-reduced basis of Λ with
parameter δ = 3/4, and let b^∨_1, . . . , b^∨_m be its dual basis. For every j ∈ [m],
∥b_j∥₂∥b^∨_j∥₂ ≤ 4^m."

For linearly independent `b₁, …, b_m ∈ ℝ^d` that are LLL-reduced with `δ = 3/4`, and vectors
`b^∨_j` in their real span with `⟨b_i, b^∨_j⟩ = δ_ij` (the dual basis of Definition 2.5), every
`‖b_j‖‖b^∨_j‖ ≤ 4^m`.

**Formalization Note.** The rank `m` and the ambient dimension `d` are independent (`m ≤ d` follows
from linear independence); the square case is not assumed. The dual basis is given by its defining
properties, which determine it uniquely. -/
theorem lemma_2_6 {m d : ℕ} (b bd : Fin m → EuclideanSpace ℝ (Fin d))
    (hb : LinearIndependent ℝ b) (hred : IsLLLReduced (3 / 4) b)
    (hspan : ∀ j, bd j ∈ Submodule.span ℝ (Set.range b))
    (hdual : ∀ i j, ⟪b i, bd j⟫_ℝ = if i = j then 1 else 0) :
    ∀ j, ‖b j‖ * ‖bd j‖ ≤ 4 ^ m := by sorry

end IntQuotHNP
