-- Prove2me | Theorems.Thm_ModLatSVP_lemma_2_3
-- name    : ModLatSVP.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:46.846933+00:00
-- url     : https://prove2.me/theorems/da669a9d-1483-46fc-9f77-07ced285f6f6
-- title:
--   Lemma 2.3 — under the search conditions, $\prod_{i=1}^r\max\{1,R/H_i\}\le2^{r+1}r^{r/2}\rho^{r/2}$
-- statement:
--   Let $M$ be a module of rank $r\ge2$ over a totally real or CM field $K$, $\rho=\mathrm{rd}(K)$, with a module flag whose blocks have minima $H_1,\dots,H_r$. If the flag satisfies the search conditions at radius $R$, then
--
--   $$\prod_{i=1}^{r}\max\{1,R/H_i\}\le 2^{r+1}\,r^{r/2}\,\rho^{r/2}.$$
--
--   The product of the blockwise ratios controls the number of nodes of a backward (Fincke–Pohst-type) enumeration over the blocks; the bound depends on $r$ and $\rho$ only, not on the field degree, which is what keeps the enumerations of the paper single-exponential.
--
--   Differences from the source:
--   - encoding: a module flag 0 = V_0 ⊂ ⋯ ⊂ V_r = M ⊗ ℚ of a rank-r module M → the module ℤ^{r×d} written in an adapted basis, V_i spanned by the first i blocks, action matrices block upper triangular (IsModuleFlag); reason: every flag has an adapted basis (§2.2, App. B.2) and every quantity involved is invariant under the change of basis
--   - encoding: G_i = det(L_i)^{1/d} → (g_i / g_{i−1})^{1/(2d)}, g_i the principal minor of the Gram matrix on the first i blocks; reason: det(L_i)² = g_i / g_{i−1} by the Schur-complement formula (43)
--   - generalization: a module in the input model, with positive definite rational Gram matrix G → any positive definite real Gram matrix G; reason: specializes to rational G by casting; the proof does not use rationality
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Lemma 2.3, §2.4, (9), p.16 (PDF p.16)

import Mathlib
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_SearchCond

open NumberField

namespace ModLatSVP

/-- **Lemma 2.3, §2.4, p.16.** Kim, Lee, Son, *Exact SVP and CVP in Structured Lattices: Polynomial-Space
Algorithms and Reductions*, STOC 2027 submission (manuscript sha256 e7151fad…): "Let a flag of rank
r ≥ 2 satisfy the search conditions at radius R. Then ∏_{i=1}^{r} max{1, R/H_i} ≤ 2^{r+1} r^{r/2} ρ^{r/2}."

For a rank-`r` module (`r ≥ 2`) over a totally real or CM field `K` with a module flag satisfying the
search conditions at radius `R`, the product of the blockwise ratios is at most
`2^{r+1} r^{r/2} rd(K)^{r/2}`.

**Formalization Note.** The flag is written in an adapted basis (`IsModuleFlag`); `H_i = blockMin`, and
the search conditions are `SearchCond G r R`, which include `R > 0`. -/
theorem lemma_2_3 (K : Type*) [Field K] [NumberField K] (hK : IsTotallyReal K ∨ IsCMField K)
    (τ : K ≃ₐ[ℚ] K) (hτ : IsStar K τ) (r d : ℕ) (hr : 2 ≤ r)
    (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (φ : K →+* Matrix (Fin r × Fin d) (Fin r × Fin d) ℚ)
    (hM : IsModuleFlag K τ r d G φ) (R : ℝ) (hS : SearchCond G r R) :
    ∏ i ∈ Finset.Icc 1 r, max 1 (R / blockMin G i) ≤
      (2 : ℝ) ^ (r + 1) * (r : ℝ) ^ ((r : ℝ) / 2) * rd K ^ ((r : ℝ) / 2) := by sorry

end ModLatSVP
