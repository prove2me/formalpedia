-- Prove2me | Theorems.Thm_MatrixLeeSidford_lemma_5_6
-- name    : MatrixLeeSidford.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:38:08.182392+00:00
-- url     : https://prove2.me/theorems/c84e9207-702e-434f-80af-7f8240fadbb9
-- title:
--   Lemma 5.6 — gradient and proxy Hessian
-- statement:
--   Throughout, $A_1,\dots,A_m,C$ are real symmetric $n\times n$ matrices satisfying the standing assumptions (4.3): $\Omega=\{y:S(y)\succ0\}\neq\emptyset$, the $A_i$ are linearly independent, and $\bigcap_i\ker A_i=\{0\}$.
--
--   Let $s\ge2$ be an integer.
--   1. For every $y\in\Omega$ and $h\in\mathbb R^m$,
--   $$
--   \nabla\Phi_p(y)[h]=-\operatorname{tr}[M_yB_h]\qquad(5.16)
--   $$
--   and
--   $$
--   Q_y[h,h]\le\nabla^2\Phi_p(y)[h,h]\le(2s+1)Q_y[h,h],\qquad |\nabla\Phi_p(y)[h]|^2\le m\,\nabla^2\Phi_p(y)[h,h].\qquad(5.17)
--   $$
--   2. In the normalization (5.1) — the slack is $S=I$, so $B_i=A_i$, and the optimal weight is $G_*(I)=I$ — every symmetric direction $T\in\mathbb S^n$ of the slack satisfies
--   $$
--   \nabla\varphi(I)[T]=-\operatorname{tr}[MT],\qquad Q(T)\le\nabla^2\varphi(I)[T,T]\le(2s+1)Q(T),\qquad Q(T)=\operatorname{tr}[MT^2].
--   $$
--
--   Part 2 is stronger than part 1 at the base point because $T$ ranges over all of $\mathbb S^n$, not only over $\{B_h\}$.
--
--   **Formalization Note** In part 2 the coefficient family is any symmetric, linearly independent family $B_1,\dots,B_m$ with trivial common kernel whose optimal weight at $S=I$ is $I$; $\nabla\varphi(I)[T]$ and $\nabla^2\varphi(I)[T,T]$ are the first and second derivatives at $t=0$ of $t\mapsto\varphi(I+tT)$.
--
--   Differences from the source:
--   - encoding: Aᵢ, C ∈ Sⁿ, y, h ∈ ℝᵐ → real n×n matrices with IsHermitian hypotheses; y, h ∈ EuclideanSpace ℝ (Fin m); reason: Lean representation of the same objects
--   - generalization: s := 2⌈log(2mn)⌉ (Definition 5.1, fixed for Section 5) → every integer s ≥ 2; reason: the proof does not use the value of s; sParam m n ≥ 2 for m, n ≥ 1, so the statement specializes to the source's
--   - encoding: G_*(y), the unique minimizer of f_y → optWeightAt / optWeight, a chosen minimizer (junk 0 if none exists); reason: by Lemma 4.4 the minimizer exists and is unique under (4.3), so the chosen one is G_*
--   - encoding: Q_y ⪯ ∇²Φ_p(y) ⪯ (2s+1)Q_y (Loewner order of forms) → inequalities of the quadratic forms for every h, with ∇²Φ_p(y)[h, h] = iteratedFDeriv ℝ 2; reason: the Loewner order of quadratic forms is the pointwise order of their values
--   - encoding: 'in the normalization (5.1)'; ∇φ(I)[T], ∇²φ(I)[T, T] → for every family B with the conditions of (4.3) and optWeight B 1 s = 1; deriv and iteratedDeriv 2 at 0 of t ↦ φ(I + tT); reason: (5.1) is S = I and G_*(I) = I; derivatives of φ along the line I + tT are the directional derivatives
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Lemma 5.6, Eqs. (5.16)–(5.17), p.43

import Mathlib
import Definitions.Def_MatrixLeeSidford_Phi__87229e
import Definitions.Def_MatrixLeeSidford_Mmat
import Definitions.Def_MatrixLeeSidford_Qform
import Definitions.Def_MatrixLeeSidford_dualRegion

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **Lemma 5.6 (Gradient and proxy Hessian)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.43). For every `y ∈ Ω` and `h ∈ ℝᵐ`,
`∇Φ_p(y)[h] = −tr[M_y B_h]` (5.16), `Q_y ⪯ ∇²Φ_p(y) ⪯ (2s+1) Q_y` and `|∇Φ_p(y)[h]|² ≤ m ∇²Φ_p(y)[h,h]`
(5.17). In the normalization (5.1), every direction `T ∈ Sⁿ` of the slack satisfies
`∇φ(I)[T] = −tr[M T]` and `Q(T) ≤ ∇²φ(I)[T, T] ≤ (2s+1) Q(T)`, `Q(T) := tr[M T²]`.

**Formalization Note** The standing assumptions (4.3) (p.32) are hypotheses: `Aᵢ, C` symmetric, `Ω ≠ ∅`, the `Aᵢ`
linearly independent, `⋂ᵢ ker Aᵢ = {0}`. Stated for every integer `s ≥ 2`. The normalized clause quantifies
over every coefficient family `B` (symmetric, linearly independent, `⋂ᵢ ker Bᵢ = {0}`) whose
optimal weight at the slack `S = I` is `G_*(I) = I` — this is (5.1), where `Bᵢ = Aᵢ`; there
`∇φ(I)[T]`, `∇²φ(I)[T,T]` are the first and second derivatives at `t = 0` of `t ↦ φ(I + tT)`, and
`M = Mmat B 1 s`. -/
theorem lemma_5_6 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (hΩ : (dualRegion A C).Nonempty) (hlin : LinearIndependent ℝ A)
    (hker : ∀ v : Fin n → ℝ, (∀ i, A i *ᵥ v = 0) → v = 0)
    (s : ℕ) (hs : 2 ≤ s) :
    (∀ y ∈ dualRegion A C, ∀ h : EuclideanSpace ℝ (Fin m),
      let S := slack A C y
      fderiv ℝ (Phi A C s) y h = -(Mmat A S s * Bdir A S h).trace ∧
      Qform A S s h ≤ iteratedFDeriv ℝ 2 (Phi A C s) y (fun _ => h) ∧
      iteratedFDeriv ℝ 2 (Phi A C s) y (fun _ => h) ≤ (2 * (s : ℝ) + 1) * Qform A S s h ∧
      (fderiv ℝ (Phi A C s) y h) ^ 2 ≤ (m : ℝ) * iteratedFDeriv ℝ 2 (Phi A C s) y (fun _ => h)) ∧
    (∀ B : Fin m → Matrix (Fin n) (Fin n) ℝ, (∀ i, (B i).IsHermitian) → LinearIndependent ℝ B →
      (∀ v : Fin n → ℝ, (∀ i, B i *ᵥ v = 0) → v = 0) → optWeight B 1 s = 1 →
      ∀ T : Matrix (Fin n) (Fin n) ℝ, T.IsHermitian →
        deriv (fun t : ℝ => phi B (1 + t • T) s) 0 = -(Mmat B 1 s * T).trace ∧
        (Mmat B 1 s * T ^ 2).trace ≤ iteratedDeriv 2 (fun t : ℝ => phi B (1 + t • T) s) 0 ∧
        iteratedDeriv 2 (fun t : ℝ => phi B (1 + t • T) s) 0 ≤
          (2 * (s : ℝ) + 1) * (Mmat B 1 s * T ^ 2).trace) := by sorry

end MatrixLeeSidford
