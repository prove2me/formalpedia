-- Prove2me | Theorems.Thm_MatrixLeeSidford_eq_5_22
-- name    : MatrixLeeSidford.eq_5_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:33.159562+00:00
-- url     : https://prove2.me/theorems/508fcef8-ed01-4aed-b263-114f71190de4
-- title:
--   Eq. (5.22) — third-derivative bound $|\nabla^3\Phi_p(y)[h,h,h]|\le150s\,v^{3/2}$
-- statement:
--   Throughout, $A_1,\dots,A_m,C$ are real symmetric $n\times n$ matrices satisfying the standing assumptions (4.3): $\Omega=\{y:S(y)\succ0\}\neq\emptyset$, the $A_i$ are linearly independent, and $\bigcap_i\ker A_i=\{0\}$.
--
--   Let $m\ge1$, $s=2\lceil\log(2mn)\rceil$ (Definition 5.1), $y\in\Omega$, $h\in\mathbb R^m$, and $v=\nabla^2\Phi_p(y)[h,h]$. Then
--   $$
--   \big|\nabla^3\Phi_p(y)[h,h,h]\big|\le\big(120s+9\sqrt{2s+1}+3\big)v^{3/2}\le150s\,v^{3/2}.
--   $$
--   After scaling by $\alpha=10^6s^2$ this gives the self-concordance inequality $|\nabla^3F|\le2(\nabla^2F)^{3/2}$ for $F=\alpha\Phi_p$.
--
--   Differences from the source:
--   - encoding: Aᵢ, C ∈ Sⁿ, y, h ∈ ℝᵐ → real n×n matrices with IsHermitian hypotheses; y, h ∈ EuclideanSpace ℝ (Fin m); reason: Lean representation of the same objects
--   - encoding: m a positive integer (Section 3.1) → hypothesis 0 < m; reason: excludes only m = 0, where s = 2⌈log 0⌉ is undefined
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Eq. (5.22), p.47

import Mathlib
import Definitions.Def_MatrixLeeSidford_Phi__87229e
import Definitions.Def_MatrixLeeSidford_sParam
import Definitions.Def_MatrixLeeSidford_dualRegion

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **Eq. (5.22)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.47). For `s` as in Definition 5.1, every `y ∈ Ω` and `h ∈ ℝᵐ`, with
`v := ∇²Φ_p(y)[h, h]`: `|∇³Φ_p(y)[h, h, h]| ≤ (120s + 9√(2s+1) + 3) v^{3/2} ≤ 150 s v^{3/2}`.

**Formalization Note** The standing assumptions (4.3) (p.32) are hypotheses: `Aᵢ, C` symmetric, `Ω ≠ ∅`, the `Aᵢ`
linearly independent, `⋂ᵢ ker Aᵢ = {0}`. `s = sParam m n = 2⌈log(2mn)⌉` and `m ≥ 1` (Section 3.1).
Derivatives are `iteratedFDeriv`. -/
theorem eq_5_22 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (hΩ : (dualRegion A C).Nonempty) (hlin : LinearIndependent ℝ A)
    (hker : ∀ v : Fin n → ℝ, (∀ i, A i *ᵥ v = 0) → v = 0)
    (hm : 0 < m) (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ dualRegion A C)
    (h : EuclideanSpace ℝ (Fin m)) :
    let s := sParam m n
    let v := iteratedFDeriv ℝ 2 (Phi A C s) y (fun _ => h)
    |iteratedFDeriv ℝ 3 (Phi A C s) y (fun _ => h)| ≤
      (120 * (s : ℝ) + 9 * Real.sqrt (2 * s + 1) + 3) * v ^ ((3 : ℝ) / 2) ∧
    (120 * (s : ℝ) + 9 * Real.sqrt (2 * s + 1) + 3) * v ^ ((3 : ℝ) / 2) ≤
      150 * (s : ℝ) * v ^ ((3 : ℝ) / 2) := by sorry

end MatrixLeeSidford
