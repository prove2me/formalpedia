-- Prove2me | Theorems.Thm_JinMaoSubsetSum_lemma_9_3_shell_volume
-- name    : JinMaoSubsetSum.lemma_9_3_shell_volume
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:39:10.680042+00:00
-- url     : https://prove2.me/theorems/f785f90a-61ec-4cc1-9de9-7c026b756906
-- title:
--   Lemma 9.3 — quotient-shell volume $\le d(a+b)\rho(1+a\rho)^{d-1}\mathrm{vol}_d(\pi_\Lambda K)$
-- statement:
--   **Lemma 9.3.** Let $\Lambda\subseteq\mathbb R^d$ be a lattice and $K,D\subseteq\mathbb R^d$ convex bodies, $D$ origin-symmetric, such that $K$ contains a translate of $\rho^{-1}D$ for some $\rho>0$. Then for all $a,b\ge0$,
--   $$
--   \mathrm{vol}_d\bigl(\pi_\Lambda(K+aD)\setminus\pi_\Lambda(K\ominus bD)\bigr)\ \le\ d(a+b)\rho(1+a\rho)^{d-1}\,\mathrm{vol}_d(\pi_\Lambda K).
--   $$
--
--   The shell between an outer and an inner parallel body of $K$ has small volume in the quotient when $K$ is fat relative to $D$; this bounds the number of subset sums the algorithm must find near the boundary of the zonotope.
--
--   **Formalization Note** The quotient set difference is the image of $E=(K+aD)\setminus((K\ominus bD)+\Lambda)$, so the left side is `qvol Λ E`. $K\ominus bD$ may be empty. At $d=0$ the right side is $0$ and so is the left.
--
--   Differences from the source:
--   - encoding: vol_d(π_Λ(K + aD) \ π_Λ(K ⊖ bD)) → qvol Λ of (K + aD) \ ((K ⊖ bD) + Λ); reason: this set's image in ℝ^d/Λ is exactly π_Λ(K + aD) \ π_Λ(K ⊖ bD)
-- source:
--   Jin, Mao, Subset Sum in Almost-Linear Time, arXiv:2610.20742v1 (sha256 8b604948862d9188e922b8abf95831fde3a3699e26d39177d20a1460e31a926a), Lemma 9.3, p.49 (PDF p.51)

import Mathlib
import Definitions.Def_JinMaoSubsetSum_zonotope
import Definitions.Def_JinMaoSubsetSum_qvol

set_option autoImplicit false

open scoped Pointwise

namespace JinMaoSubsetSum

/-- **Lemma 9.3** (Jin, Mao, *Subset Sum in Almost-Linear Time*, arXiv:2610.20742v1, p.49): "Let
Λ ⊆ ℝ^d be a lattice, and K, D ⊆ ℝ^d be convex bodies, where D is origin-symmetric, and K contains
a translate of ρ^{−1}D for some ρ > 0. Then, for all a, b ≥ 0,
vol_d(π_Λ(K + aD) \ π_Λ(K ⊖ bD)) ≤ d(a + b)ρ(1 + aρ)^{d−1} vol_d(π_Λ K)."

**Formalization Note.** `Λ` is a discrete additive subgroup of any rank; `vol_d(π_Λ(·))` is
`qvol Λ`. The set `π_Λ(K + aD) \ π_Λ(K ⊖ bD)` of the quotient is the image of
`E = (K + aD) \ ((K ⊖ bD) + Λ)`: a point of `K + aD` maps outside `π_Λ(K ⊖ bD)` iff it is not
congruent modulo `Λ` to a point of `K ⊖ bD`; so the left side is `qvol Λ E`. `K ⊖ bD` may be empty.
At `d = 0` the natural-number exponent `d − 1` is `0` and the factor `d` makes the right side `0`
(the left side is then `0` as well). -/
theorem lemma_9_3_shell_volume {d : ℕ} (Λ : AddSubgroup (Fin d → ℝ)) [DiscreteTopology Λ]
    (K D : Set (Fin d → ℝ)) (hK : IsConvexBody K) (hD : IsConvexBody D) (hDs : IsOriginSymm D)
    (ρ : ℝ) (hρ : 0 < ρ) (hKD : ∃ x : Fin d → ℝ, (fun y => x + y) '' (ρ⁻¹ • D) ⊆ K)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    qvol Λ ((K + a • D) \ (erosion K (b • D) + (Λ : Set (Fin d → ℝ)))) ≤
      ENNReal.ofReal ((d : ℝ) * (a + b) * ρ * (1 + a * ρ) ^ (d - 1)) * qvol Λ K := by sorry

end JinMaoSubsetSum
