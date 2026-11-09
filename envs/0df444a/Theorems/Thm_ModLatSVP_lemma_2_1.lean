-- Prove2me | Theorems.Thm_ModLatSVP_lemma_2_1
-- name    : ModLatSVP.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:52.037193+00:00
-- url     : https://prove2.me/theorems/bfc4bca3-78c0-4a3f-93a1-e45f0b52584c
-- title:
--   Lemma 2.1 — rank-one modules: $G_L\le\sqrt{\rho/d}\,H$, $L^*$ is a module, $\lambda_1\lambda_1^*\ge d/\rho$, $\mu\le2\rho\lambda_1$
-- statement:
--   Let $K$ be a totally real or CM field of degree $d$ with root discriminant $\rho=\mathrm{rd}(K)$, and let $L$ be a **rank-one module** over $K$: a lattice of dimension $d$ with an $\mathcal O_K$-action and a compatible inner product. Let $H=\lambda_1(L)$ and $G_L=\det(L)^{1/d}$. Then
--
--   1. $G_L\le\sqrt{\rho/d}\;H$;
--   2. the dual lattice $L^*$ is again a rank-one module: every $\alpha\in\mathcal O_K$ maps $L^*$ into itself;
--   3. $$\lambda_1(L)\,\lambda_1(L^*)\ge\frac d\rho ;$$
--   4. $$\mu(L)\le 2\rho\,\lambda_1(L).$$
--
--   Rank-one modules are the blocks of every module flag, and these inequalities bound their shape in terms of $\rho$ alone; they enter the reduced-flag bound (7), Lemma 2.3, and the CVP search radius.
--
--   Differences from the source:
--   - encoding: L is a rank-one module over K; 'L* is also a rank-one module' → ℤ^ι with |ι| = [K:ℚ] and a compatible 𝒪_K-action (IsCompatible); the conclusion that the ℝ-linear extension of every α ∈ 𝒪_K maps L* into L*; reason: ℚ^ι is then a one-dimensional K-space; L* spans the same d-dimensional space, so it has rank one once it is an 𝒪_K-module
--   - generalization: a module in the input model, with positive definite rational Gram matrix G → any positive definite real Gram matrix G; reason: specializes to rational G by casting; the proof does not use rationality
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Lemma 2.1, §2.3, p.13 (PDF p.13)

import Mathlib
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_lam1
import Definitions.Def_ModLatSVP_IsCompatible

open NumberField Matrix

namespace ModLatSVP

/-- **Lemma 2.1, §2.3, p.13.** Kim, Lee, Son, *Exact SVP and CVP in Structured Lattices: Polynomial-Space
Algorithms and Reductions*, STOC 2027 submission (manuscript sha256 e7151fad…): "Let L be a rank-one
module over K, with minimum H = λ₁(L) and normalized determinant G_L = det(L)^{1/d}. Then
G_L ≤ √(ρ/d) H. Moreover, L* is also a rank-one module, and λ₁(L)λ₁(L*) ≥ d/ρ, µ(L) ≤ 2ρλ₁(L)."

Here `K` is totally real or CM with involution `τ`, `d = [K : ℚ]`, `ρ = rd(K)`, and `L = ℤ^ι` with
`|ι| = d` is an `𝒪_K`-module with compatible Gram matrix `G`. Conclusions:
1. `det(L)^{1/d} ≤ √(ρ/d) · λ₁(L)`;
2. the action of every `α ∈ 𝒪_K` (extended `ℝ`-linearly to the span) maps `L*` into `L*`;
3. `λ₁(L) λ₁(L*) ≥ d/ρ`;
4. `µ(L) ≤ 2ρ λ₁(L)`.

**Formalization Note.** "Rank one" is `|ι| = [K : ℚ]`: `ℚ^ι` is then a one-dimensional `K`-vector space.
That `L*` is a rank-one module is stated as conclusion 2 (it spans the same `d`-dimensional space, so it
has rank one once it is a module). -/
theorem lemma_2_1 (K : Type*) [Field K] [NumberField K] (hK : IsTotallyReal K ∨ IsCMField K)
    (τ : K ≃ₐ[ℚ] K) (hτ : IsStar K τ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = Module.finrank ℚ K)
    (G : Matrix ι ι ℝ) (φ : K →+* Matrix ι ι ℚ) (hL : IsCompatible K τ G φ) :
    latDet G ^ ((1 : ℝ) / Module.finrank ℚ K) ≤
        Real.sqrt (rd K / Module.finrank ℚ K) * lam1 G ∧
      (∀ α : 𝓞 K, ∀ c ∈ dualLat G, (φ (α : K)).map (fun q : ℚ => (q : ℝ)) *ᵥ c ∈ dualLat G) ∧
      (Module.finrank ℚ K : ℝ) / rd K ≤ lam1 G * lam1Dual G ∧
      covRad G ≤ 2 * rd K * lam1 G := by sorry

end ModLatSVP
