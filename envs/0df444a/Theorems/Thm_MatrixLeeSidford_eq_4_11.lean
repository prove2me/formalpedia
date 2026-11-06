-- Prove2me | Theorems.Thm_MatrixLeeSidford_eq_4_11
-- name    : MatrixLeeSidford.eq_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:33:59.840297+00:00
-- url     : https://prove2.me/theorems/aa55cf01-52d5-41f4-ae6c-eacc0cb6ef4c
-- title:
--   Eq. (4.11) — Hessian of $f_y$
-- statement:
--   Throughout, $A_1,\dots,A_m,C$ are real symmetric $n\times n$ matrices satisfying the standing assumptions (4.3): $\Omega=\{y:S(y)\succ0\}\neq\emptyset$, the $A_i$ are linearly independent, and $\bigcap_i\ker A_i=\{0\}$.
--
--   Let $s\ge2$ be an integer, $y\in\Omega$ and $G\succ0$. For every symmetric $V\in\mathbb S^m$,
--   $$
--   \nabla^2 f_y(G)[V,V]=\big\|G^{-1/2}VG^{-1/2}\big\|_F^2+\sum_{a=0}^{s-2}\big\|L_y(G)^{a/2}\,L_y(V)\,L_y(G)^{(s-2-a)/2}\big\|_F^2 .
--   $$
--   In particular $f_y$ is strictly convex on the positive definite cone, which gives uniqueness of the optimal weight.
--
--   **Formalization Note** $\nabla^2f_y(G)[V,V]$ is the second derivative at $t=0$ of $t\mapsto f_y(G+tV)$; the real powers of the positive definite matrix $L_y(G)$ are spectral powers.
--
--   Differences from the source:
--   - encoding: Aᵢ, C ∈ Sⁿ, y, h ∈ ℝᵐ → real n×n matrices with IsHermitian hypotheses; y, h ∈ EuclideanSpace ℝ (Fin m); reason: Lean representation of the same objects
--   - encoding: ∇²f_y(G)[V, V] → iteratedDeriv 2 of t ↦ f_y(G + tV) at 0; reason: the second derivative along the line through G in direction V is the Hessian form
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Eq. (4.11), p.35

import Mathlib
import Definitions.Def_MatrixLeeSidford_fObj
import Definitions.Def_MatrixLeeSidford_matRpow
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_MatrixLeeSidford_dualRegion

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **Eq. (4.11)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.35). For `G ≻ 0` and every symmetric `V ∈ Sᵐ`,
`∇²f_y(G)[V, V] = ‖G^{-1/2} V G^{-1/2}‖_F² + ∑_{a=0}^{s−2} ‖L_y(G)^{a/2} L_y(V) L_y(G)^{(s−2−a)/2}‖_F²`.

**Formalization Note** The standing assumptions (4.3) (p.32) are hypotheses: `Aᵢ, C` symmetric, `Ω ≠ ∅`, the `Aᵢ`
linearly independent, `⋂ᵢ ker Aᵢ = {0}`. `∇²f_y(G)[V, V]` is the second derivative at `t = 0` of
`t ↦ f_y(G + tV)`; real powers are `matRpow`; `s ≥ 2` is an integer (Definition 4.3). -/
theorem eq_4_11 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (hΩ : (dualRegion A C).Nonempty) (hlin : LinearIndependent ℝ A)
    (hker : ∀ v : Fin n → ℝ, (∀ i, A i *ᵥ v = 0) → v = 0)
    (s : ℕ) (hs : 2 ≤ s) (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ dualRegion A C)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosDef) (V : Matrix (Fin m) (Fin m) ℝ)
    (hV : V.IsHermitian) :
    let S := slack A C y
    let L := Lmap A S G
    iteratedDeriv 2 (fun t : ℝ => fObj A S s (G + t • V)) 0 =
      LowRankMEG.frobNorm (matRpow (-(1 / 2)) G * V * matRpow (-(1 / 2)) G) ^ 2 +
        ∑ a ∈ Finset.range (s - 1),
          LowRankMEG.frobNorm (matRpow ((a : ℝ) / 2) L * Lmap A S V *
            matRpow (((s : ℝ) - 2 - a) / 2) L) ^ 2 := by sorry

end MatrixLeeSidford
