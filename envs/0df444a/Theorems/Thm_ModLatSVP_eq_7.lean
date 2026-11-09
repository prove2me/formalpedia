-- Prove2me | Theorems.Thm_ModLatSVP_eq_7
-- name    : ModLatSVP.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:12:52.15242+00:00
-- url     : https://prove2.me/theorems/a59919e5-4f66-40ab-87a3-72e5b0d134eb
-- title:
--   (7) — reduced flags: $H_i\le\sqrt{kd}\,(\prod_{u=i}^jG_u)^{1/k}\le\sqrt{k\rho}\,(\prod_{u=i}^jH_u)^{1/k}$
-- statement:
--   Let $M$ be a rank-$r$ module over a totally real or CM field $K$ of degree $d$, $\rho=\mathrm{rd}(K)$, with a module flag whose blocks have minima $H_u$ and normalized determinants $G_u$. Suppose the flag is reduced at index $i$, and let $i\le j\le r$ and $k=j-i+1$. Then
--
--   $$H_i\le\sqrt{kd}\,\Big(\prod_{u=i}^{j}G_u\Big)^{1/k}\le\sqrt{k\rho}\,\Big(\prod_{u=i}^{j}H_u\Big)^{1/k}.$$
--
--   The first inequality is Minkowski's theorem on the projected prefix $\pi_{V_{i-1}^\perp}M_j$, the second is Lemma 2.1 on each block. Together they say that reducedness keeps consecutive block minima from dropping too fast, which is the input to Lemma 2.3.
--
--   Differences from the source:
--   - encoding: a module flag 0 = V_0 ⊂ ⋯ ⊂ V_r = M ⊗ ℚ of a rank-r module M → the module ℤ^{r×d} written in an adapted basis, V_i spanned by the first i blocks, action matrices block upper triangular (IsModuleFlag); reason: every flag has an adapted basis (§2.2, App. B.2) and every quantity involved is invariant under the change of basis
--   - encoding: G_i = det(L_i)^{1/d} → (g_i / g_{i−1})^{1/(2d)}, g_i the principal minor of the Gram matrix on the first i blocks; reason: det(L_i)² = g_i / g_{i−1} by the Schur-complement formula (43)
--   - generalization: a module in the input model, with positive definite rational Gram matrix G → any positive definite real Gram matrix G; reason: specializes to rational G by casting; the proof does not use rationality
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §2.3, (7), p.14 (PDF p.14)

import Mathlib
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_IsModuleFlag

open NumberField

namespace ModLatSVP

/-- **(7), §2.3, p.14: the geometric bound for reduced flags.** Kim, Lee, Son, *Exact SVP and CVP in
Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript
sha256 e7151fad…): "Suppose that the flag is reduced at index i, and let j ≥ i and k = j − i + 1. … By
Minkowski's theorem and Lemma 2.1, H_i ≤ √(kd) (∏_{u=i}^{j} G_u)^{1/k} ≤ √(kρ) (∏_{u=i}^{j} H_u)^{1/k}."

For a rank-`r` module over a totally real or CM field `K` (`d = [K : ℚ]`, `ρ = rd(K)`) with a module flag
reduced at index `i`, and `1 ≤ i ≤ j ≤ r`, `k = j − i + 1`, both inequalities of (7) hold.

**Formalization Note.** The flag is written in an adapted basis (`IsModuleFlag`); `H_u = blockMin`,
`G_u = normDet`. `k = j − i + 1 ≥ 1` since `i ≤ j`. -/
theorem eq_7 (K : Type*) [Field K] [NumberField K] (hK : IsTotallyReal K ∨ IsCMField K)
    (τ : K ≃ₐ[ℚ] K) (hτ : IsStar K τ) (r d : ℕ)
    (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (φ : K →+* Matrix (Fin r × Fin d) (Fin r × Fin d) ℚ)
    (hM : IsModuleFlag K τ r d G φ) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ r)
    (hred : ReducedAt G r i) :
    blockMin G i ≤ Real.sqrt (((j - i + 1 : ℕ) : ℝ) * d) *
        (∏ u ∈ Finset.Icc i j, normDet G u) ^ ((1 : ℝ) / (j - i + 1 : ℕ)) ∧
      Real.sqrt (((j - i + 1 : ℕ) : ℝ) * d) *
          (∏ u ∈ Finset.Icc i j, normDet G u) ^ ((1 : ℝ) / (j - i + 1 : ℕ)) ≤
        Real.sqrt (((j - i + 1 : ℕ) : ℝ) * rd K) *
          (∏ u ∈ Finset.Icc i j, blockMin G u) ^ ((1 : ℝ) / (j - i + 1 : ℕ)) := by sorry

end ModLatSVP
