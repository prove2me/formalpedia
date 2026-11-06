-- Prove2me | Theorems.Thm_MatrixLeeSidford_lemma_5_8
-- name    : MatrixLeeSidford.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:37:56.807729+00:00
-- url     : https://prove2.me/theorems/39f770fd-070e-47e1-bd28-30133be7c422
-- title:
--   Lemma 5.8 — ellipsoid rounding and the local norm
-- statement:
--   Throughout, $A_1,\dots,A_m,C$ are real symmetric $n\times n$ matrices satisfying the standing assumptions (4.3): $\Omega=\{y:S(y)\succ0\}\neq\emptyset$, the $A_i$ are linearly independent, and $\bigcap_i\ker A_i=\{0\}$.
--
--   Let $s\ge2$ be an integer, $y\in\Omega$ and $h\in\mathbb R^m$, with $G_*=G_*(y)$ and $Q_y$ the proxy Hessian. Then
--   $$
--   \|B_h\|_{op}^2\le m^{1/s}\,h^\top G_*^{-1}h\le m\,n^{1/s}\,\|B_h\|_{op}^2
--   $$
--   and
--   $$
--   \|B_h\|_{op}^2\le2(mn)^{1/(s-1)}Q_y[h,h]\le2(mn)^{1/(s-1)}\nabla^2\Phi_p(y)[h,h].\qquad(5.21)
--   $$
--   For $s=2\lceil\log(2mn)\rceil$ (Definition 5.1) and $m\ge1$, the factor $2(mn)^{1/(s-1)}$ is less than $9$.
--
--   In terms of ellipsoids, the first chain says $m^{-1/(2s)}E_{G_*}\subseteq K_y\subseteq(m^{1-1/s}n^{1/s})^{1/2}E_{G_*}$.
--
--   Differences from the source:
--   - encoding: Aᵢ, C ∈ Sⁿ, y, h ∈ ℝᵐ → real n×n matrices with IsHermitian hypotheses; y, h ∈ EuclideanSpace ℝ (Fin m); reason: Lean representation of the same objects
--   - generalization: s := 2⌈log(2mn)⌉ (Definition 5.1) in the four inequalities → every integer s ≥ 2 in the four inequalities; the last clause at s = sParam m n; reason: the proof of the four inequalities does not use the value of s; at s = sParam m n ≥ 2 they are the source's
--   - encoding: G_*(y), the unique minimizer of f_y → optWeightAt / optWeight, a chosen minimizer (junk 0 if none exists); reason: by Lemma 4.4 the minimizer exists and is unique under (4.3), so the chosen one is G_*
--   - encoding: m a positive integer (Section 3.1) in the last clause → hypothesis 0 < m on the last clause; reason: excludes only m = 0, where log(2mn) = log 0 is undefined
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Lemma 5.8, Eq. (5.21), p.45

import Mathlib
import Definitions.Def_MatrixLeeSidford_Phi__87229e
import Definitions.Def_MatrixLeeSidford_optWeightAt
import Definitions.Def_MatrixLeeSidford_Qform
import Definitions.Def_LiqPremiaEq_opNorm
import Definitions.Def_MatrixLeeSidford_sParam
import Definitions.Def_MatrixLeeSidford_dualRegion

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **Lemma 5.8 (Ellipsoid rounding and the local norm)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.45). Let `y ∈ Ω` and
`h ∈ ℝᵐ`. Then `‖B_h‖_op² ≤ m^{1/s} hᵀG_*^{−1}h ≤ m n^{1/s} ‖B_h‖_op²`, and
`‖B_h‖_op² ≤ 2(mn)^{1/(s−1)} Q_y[h, h] ≤ 2(mn)^{1/(s−1)} ∇²Φ_p(y)[h, h]` (5.21). For `s` as in
Definition 5.1, the factor `2(mn)^{1/(s−1)}` is less than `9`.

**Formalization Note** The standing assumptions (4.3) (p.32) are hypotheses: `Aᵢ, C` symmetric, `Ω ≠ ∅`, the `Aᵢ`
linearly independent, `⋂ᵢ ker Aᵢ = {0}`. The four inequalities are stated for every integer `s ≥ 2` (their
proof does not use the value of `s`); the last clause for `s = sParam m n = 2⌈log(2mn)⌉` and
`m ≥ 1` (Section 3.1 takes `m` positive; `n ≥ 1` then follows from the hypotheses). Powers are
`Real.rpow`. -/
theorem lemma_5_8 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (hΩ : (dualRegion A C).Nonempty) (hlin : LinearIndependent ℝ A)
    (hker : ∀ v : Fin n → ℝ, (∀ i, A i *ᵥ v = 0) → v = 0)
    (s : ℕ) (hs : 2 ≤ s) (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ dualRegion A C)
    (h : EuclideanSpace ℝ (Fin m)) :
    let S := slack A C y
    let G := optWeightAt A C s y
    let b := LiqPremiaEq.opNorm (Bdir A S h)
    b ^ 2 ≤ (m : ℝ) ^ (1 / (s : ℝ)) * (h ⬝ᵥ (G⁻¹ *ᵥ h)) ∧
    (m : ℝ) ^ (1 / (s : ℝ)) * (h ⬝ᵥ (G⁻¹ *ᵥ h)) ≤ (m : ℝ) * (n : ℝ) ^ (1 / (s : ℝ)) * b ^ 2 ∧
    b ^ 2 ≤ 2 * ((m : ℝ) * n) ^ (1 / ((s : ℝ) - 1)) * Qform A S s h ∧
    2 * ((m : ℝ) * n) ^ (1 / ((s : ℝ) - 1)) * Qform A S s h ≤
      2 * ((m : ℝ) * n) ^ (1 / ((s : ℝ) - 1)) * iteratedFDeriv ℝ 2 (Phi A C s) y (fun _ => h) ∧
    (0 < m → 2 * ((m : ℝ) * n) ^ (1 / ((sParam m n : ℝ) - 1)) < 9) := by sorry

end MatrixLeeSidford
