-- Prove2me | Theorems.Thm_MatrixLeeSidford_lemma_5_7
-- name    : MatrixLeeSidford.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:47.267442+00:00
-- url     : https://prove2.me/theorems/f40f3512-7830-476d-8773-2e12172a2a2b
-- title:
--   Lemma 5.7 — first derivatives of the optimal weight
-- statement:
--   Throughout, $A_1,\dots,A_m,C$ are real symmetric $n\times n$ matrices satisfying the standing assumptions (4.3): $\Omega=\{y:S(y)\succ0\}\neq\emptyset$, the $A_i$ are linearly independent, and $\bigcap_i\ker A_i=\{0\}$.
--
--   Let $s\ge2$ be an integer.
--   1. In the normalization (5.1) (slack $S=I$, optimal weight $G_*(I)=I$), let $T\in\mathbb S^n$, $v=\nabla^2\varphi(I)[T,T]$ and $V_*=\frac{d}{dt}G_*(e^{tT})\big|_{t=0}$. Then
--   $$
--   \|V_*\|_F\le\sqrt{6v}.\qquad(5.20)
--   $$
--   2. In arbitrary coordinates: for every $y\in\Omega$ and $h\in\mathbb R^m$,
--   $$
--   \big\|G_*^{-1/2}\,\nabla G_*(y)[h]\,G_*^{-1/2}\big\|_F\le\sqrt{6\,\nabla^2\Phi_p(y)[h,h]} .
--   $$
--   The optimal weight therefore moves slowly relative to the local norm of the potential, which is the main input for the third-derivative bound.
--
--   **Formalization Note** In part 1 the coefficient family is any symmetric, linearly independent family with trivial common kernel whose optimal weight at $S=I$ is $I$, and $v$ is the second derivative at $0$ of $t\mapsto\varphi(I+tT)$. $V_*$ and $\nabla G_*(y)[h]$ are the entrywise derivatives at $t=0$ of $t\mapsto G_*(e^{tT})$ and $t\mapsto G_*(y+th)$.
--
--   Differences from the source:
--   - encoding: Aᵢ, C ∈ Sⁿ, y, h ∈ ℝᵐ → real n×n matrices with IsHermitian hypotheses; y, h ∈ EuclideanSpace ℝ (Fin m); reason: Lean representation of the same objects
--   - generalization: s := 2⌈log(2mn)⌉ (Definition 5.1, fixed for Section 5) → every integer s ≥ 2; reason: the proof does not use the value of s; sParam m n ≥ 2 for m, n ≥ 1, so the statement specializes to the source's
--   - encoding: G_*(y), the unique minimizer of f_y → optWeightAt / optWeight, a chosen minimizer (junk 0 if none exists); reason: by Lemma 4.4 the minimizer exists and is unique under (4.3), so the chosen one is G_*
--   - encoding: 'in the normalization (5.1)'; v = ∇²φ(I)[T, T]; V_* = (d/dt)G_*(e^{tT})|₀; ∇G_*(y)[h] → for every family B with the conditions of (4.3) and optWeight B 1 s = 1; iteratedDeriv 2 at 0 of t ↦ φ(I + tT); entrywise deriv at 0 of t ↦ G_*(LowRankMEG.mexp (t • T)) and t ↦ G_*(y + th); reason: same quantities; entrywise derivatives avoid a norm choice on matrices
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Lemma 5.7, Eq. (5.20), p.44

import Mathlib
import Definitions.Def_MatrixLeeSidford_Phi__87229e
import Definitions.Def_MatrixLeeSidford_optWeightAt
import Definitions.Def_LowRankMEG_mexp
import Definitions.Def_MatrixLeeSidford_matRpow
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_MatrixLeeSidford_dualRegion

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **Lemma 5.7 (First derivatives of the optimal weight)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.44). In the normalization
(5.1), let `T ∈ Sⁿ`, `v := ∇²φ(I)[T, T]` and `V_* := (d/dt) G_*(e^{tT})|_{t=0}`. Then `‖V_*‖_F ≤ √(6v)`
(5.20). In arbitrary coordinates, `‖G_*^{−1/2} ∇G_*(y)[h] G_*^{−1/2}‖_F ≤ √(6 ∇²Φ_p(y)[h, h])`.

**Formalization Note** The standing assumptions (4.3) (p.32) are hypotheses: `Aᵢ, C` symmetric, `Ω ≠ ∅`, the `Aᵢ`
linearly independent, `⋂ᵢ ker Aᵢ = {0}`. Stated for every integer `s ≥ 2`. The normalized clause quantifies
over every coefficient family `B` (symmetric, linearly independent, `⋂ᵢ ker Bᵢ = {0}`) with
`G_*(I) = I` (the normalization (5.1)); `v` is the second derivative at `0` of `t ↦ φ(I + tT)`;
`V_*` and `∇G_*(y)[h]` are entrywise derivatives in `t` at `0` of `G_*(e^{tT})` and
`G_*(y + th)`; `G_*^{−1/2}` is `matRpow (-1/2)`. -/
theorem lemma_5_7 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (hΩ : (dualRegion A C).Nonempty) (hlin : LinearIndependent ℝ A)
    (hker : ∀ v : Fin n → ℝ, (∀ i, A i *ᵥ v = 0) → v = 0)
    (s : ℕ) (hs : 2 ≤ s) :
    (∀ B : Fin m → Matrix (Fin n) (Fin n) ℝ, (∀ i, (B i).IsHermitian) → LinearIndependent ℝ B →
      (∀ v : Fin n → ℝ, (∀ i, B i *ᵥ v = 0) → v = 0) → optWeight B 1 s = 1 →
      ∀ T : Matrix (Fin n) (Fin n) ℝ, T.IsHermitian →
        LowRankMEG.frobNorm (Matrix.of fun i j => deriv (fun t : ℝ => optWeight B (LowRankMEG.mexp (t • T)) s i j) 0) ≤
          Real.sqrt (6 * iteratedDeriv 2 (fun t : ℝ => phi B (1 + t • T) s) 0)) ∧
    (∀ y ∈ dualRegion A C, ∀ h : EuclideanSpace ℝ (Fin m),
      let G := optWeightAt A C s y
      let DG : Matrix (Fin m) (Fin m) ℝ :=
        Matrix.of fun i j => deriv (fun t : ℝ => optWeightAt A C s (y + t • h) i j) 0
      LowRankMEG.frobNorm (matRpow (-(1 / 2)) G * DG * matRpow (-(1 / 2)) G) ≤
        Real.sqrt (6 * iteratedFDeriv ℝ 2 (Phi A C s) y (fun _ => h))) := by sorry

end MatrixLeeSidford
