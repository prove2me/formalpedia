-- Prove2me | Theorems.Thm_KSPolySign_lemma_2_7
-- name    : KSPolySign.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:40:29.432517+00:00
-- url     : https://prove2.me/theorems/9c7dc562-c160-446c-898c-29d9862caa44
-- title:
--   Lemma 2.7 — strict descent at light states (informal version of Lemma 5.5)
-- statement:
--   Let $y$ be a light state with at least one active coordinate. Then there are a drift $h$ and a covariance $K\succeq0$, both supported on the active coordinates, such that
--   $$h\cdot\nabla P(y)+\tfrac12\,\mathrm{tr}\big[K\,\nabla^2P(y)\big]<0,$$
--   where the gradient and Hessian are taken with respect to the active coordinates.
--
--   Equivalently, the active gradient is nonzero or the active Hessian is not positive semidefinite, so a small move decreases the potential. With the endpoint moves of Lemma 3.10 this forces a minimizer of $P$ to be a vertex of the cube. Lemma 5.5 (p.52) is the formal version, with an explicit drift and covariance.
--
--   Differences from the source:
--   - generalization: the normalized inputs Ā_i of Lemma 3.1 (F = 0) → every maintained instance: PSD rank-one C_i with ∑C_i² ⪯ I, any Hermitian F, any ρ > 0; reason: Definition 3.5 evaluates this notation with C_i in place of Ā_i, and the normalized inputs are such an instance (ζ ≤ 1); the statement specializes to the source's
--   - encoding: h and K on the active coordinates → h ∈ ℝ^k and a real PSD K ∈ ℝ^{k×k} vanishing outside the active coordinates; ∇P, ∇²P as derivatives of the potential on the face of y; reason: same objects, extended by zero
--   - encoding: matrices in ℂ^{n×n} with nonzero inputs (so n ≥ 1) → explicit hypothesis 1 ≤ n; reason: excludes only 0×0 matrices, where the program of Definition 3.3 is degenerate and P has no meaning
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 2.7, p.11 (PDF p.11); formal version Lemma 5.5, p.52 (PDF p.52)

import Mathlib
import Definitions.Def_KSPolySign_IsLight
import Definitions.Def_KSPolySign_IsInstance
import Definitions.Def_KSPolySign_grad
import Definitions.Def_KSPolySign_hess
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma 2.7 (Strict descent; informal version of Lemma 5.5).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 2.7, p.11 (PDF p.11);
formal version Lemma 5.5, p.52 (PDF p.52).

At every light state with at least one active coordinate there are a drift `h` and a covariance
`K ⪰ 0` with `h · ∇P + ½ tr[K∇²P] < 0`, gradient and Hessian taken in the active coordinates.

**Formalization Note** Stated for every maintained instance (Definition 3.5: nonzero PSD rank-one `C_i` with `∑ C_i² ⪯ I`, a fixed Hermitian `F`) and every `ρ > 0`; the normalized inputs are the case `F = 0`, `C_i = Ā_i`. `n ≥ 1` excludes `0 × 0` matrices. `h` and `K` are indexed by all coordinates and vanish outside the
active ones; `∇P`, `∇²P` are `grad`, `hess` (derivatives of the potential on the face of `y`).
`K` is a real PSD matrix. -/
theorem lemma_2_7 (n k : ℕ) (hn : 1 ≤ n) (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (hC : IsInstance C)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : F.IsHermitian) (ρ : ℝ) (hρ : 0 < ρ)
    (y : Fin k → ℝ) (hlight : IsLight C F ρ y) (hact : ∃ i, |y i| < 1) :
    ∃ (h : Fin k → ℝ) (K : Matrix (Fin k) (Fin k) ℝ), K.PosSemidef ∧
      (∀ i, ¬ |y i| < 1 → h i = 0 ∧ ∀ j, K i j = 0 ∧ K j i = 0) ∧
      ∑ i, h i * grad C F ρ y i + (1 / 2) * ∑ i, ∑ j, K i j * hess C F ρ y i j < 0 := by sorry

end KSPolySign
