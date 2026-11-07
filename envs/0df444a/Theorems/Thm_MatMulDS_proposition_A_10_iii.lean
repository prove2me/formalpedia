-- Prove2me | Theorems.Thm_MatMulDS_proposition_A_10_iii
-- name    : MatMulDS.proposition_A_10_iii
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:25.11819+00:00
-- url     : https://prove2.me/theorems/845f83b2-773e-4821-a782-6d9f6d4db6e7
-- title:
--   Proposition A.10(iii) — a positive score gives subquadratic preprocessing and fast queries
-- statement:
--   Suppose an approximate bilinear identity for a block tensor is bijective, has score $\sigma>0$, and has a strict weight function. Then for all fixed constants $0<\delta<\sigma$ and $q_0>0$ there is a constant $\gamma>0$ such that for $D=N^\delta$, arbitrary $A\in\mathbb F^{N\times D}$ and $B\in\mathbb F^{D\times N}$ admit a bilinear data structure with preprocessing time
--   $$O(N^{2-\gamma})$$
--   and query time $O(D^{q_0})$, without using any bound on rectangular matrix multiplication.
--
--   This is why the score is the quantity to maximize.
--
--   Differences from the source:
--   - encoding: $D=N^\delta$ → $D=\lceil N^\delta\rceil$, for every $N\ge1$; reason: the source rounds dimensions (§4.2, p.16)
--   - encoding: "a bilinear data structure" (Definition 4.1: uniform circuits) → a uniform family `AdmitsDS` generated from $N,D$; reason: a single circuit has no $O(s)$; the source treats these as families
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Proposition A.10(iii), p.80 (PDF p.82)

import Mathlib
import Definitions.Def_MatMulDS_IsEnlargement
import Definitions.Def_MatMulDS_UniformFamily

set_option autoImplicit false

namespace MatMulDS

variable {I K J B P : Type} [Fintype I] [Fintype K] [Fintype J] [Fintype B] [Fintype P]
  [DecidableEq I] [DecidableEq K] [DecidableEq J] [DecidableEq B] [DecidableEq P]

/-- **Proposition A.10(iii), p.80** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Suppose the identity
is bijective, `σ > 0`, and it has a strict weight function. Then for all fixed constants `0 < δ < σ` and `q0 > 0`, there is a constant `γ > 0` such that
for `D = N^δ`, arbitrary `A ∈ F^{N×D}` and `B ∈ F^{D×N}` admit a bilinear data structure with preprocessing time `O(N^{2−γ})` and query time `O(D^{q0})`.

**Formalization Note** `D = N^δ` is rounded up, `D = ⌈N^δ⌉`, for every `N ≥ 1`; `O(·)` is `C ·` with `C` fixed before `N`. The conclusion mentions no bound on
`ω`, which is the clause "without using any bound on rectangular matrix multiplication". The choice `π = U` is part of the proof, so it does not appear in
the conclusion. -/
theorem proposition_A_10_iii (F : Type) [Field F] [CharZero F] [DecidableEq F]
    (T : BlockTensor I K J B) (D : IdentityData I K J P) (hD : D.Computes T)
    (hbij : IsBijective T P) (hσ : 0 < score T P) (hweight : HasStrictWeight T D)
    (δ q0 : ℝ) (hδ : 0 < δ) (hδσ : δ < score T P) (hq0 : 0 < q0) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
      AdmitsDS F (fun N Dm => 1 ≤ N ∧ Dm = ⌈(N : ℝ) ^ δ⌉₊)
        (fun N _ => C * (N : ℝ) ^ (2 - γ)) (fun _ Dm => C * (Dm : ℝ) ^ q0) := by sorry

end MatMulDS
