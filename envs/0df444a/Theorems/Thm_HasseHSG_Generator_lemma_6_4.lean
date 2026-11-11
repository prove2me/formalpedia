-- Prove2me | Theorems.Thm_HasseHSG_Generator_lemma_6_4
-- name    : HasseHSG.Generator.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:36:34.067564+00:00
-- url     : https://prove2.me/theorems/7baec8af-cef3-40a6-af43-4e9fd142d361
-- title:
--   Lemma 6.4 (Casoratian) — $\det M_\sigma(g)\neq0$ iff $g_1,\dots,g_m$ are $L^\sigma$-linearly independent
-- statement:
--   Let $(L,\sigma)$ be a difference field: a field $L$ with a ring endomorphism $\sigma:L\to L$. Let $L^\sigma=\{u\in L:\sigma(u)=u\}$ be its fixed field and $g_1,\dots,g_m\in L$. Let $M_\sigma(g_1,\dots,g_m)$ be the $m\times m$ matrix with entries $\sigma^i(g_j)$, $0\le i\le m-1$. Then
--
--   $$\det M_\sigma(g_1,\dots,g_m)\neq0\iff g_1,\dots,g_m\ \text{are}\ L^\sigma\text{-linearly independent}.$$
--
--   Linear independence means that whenever $u_1,\dots,u_m\in L^\sigma$ satisfy $\sum_j u_jg_j=0$, every $u_j$ is $0$. This is the classical Casoratian criterion of difference algebra. Together with $L^{\sigma_q}=F(q)$ (Theorem 5.9) and Lemma 6.3, it gives Theorem 6.2.
--
--   Differences from the source:
--   - generalization: (L, σ) a difference field; the preceding paragraph says 'an arbitrary field automorphism' → σ any ring endomorphism of the field L; reason: p. 16 defines a difference field with an endomorphism and the proof uses only injectivity; automorphisms are a special case
--   - encoding: L^σ-linear independence → ∀ c : Fin m → L with σ (c j) = c j, Σ c j g j = 0 → c = 0; reason: the definition of linear independence over the fixed field
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 29, Lemma 6.4

import Mathlib
import Definitions.Def_HasseHSG_Generator_Wronskian

namespace HasseHSG.Generator

/-- Lemma 6.4 (Casoratian, p. 29), for a field `L` with a ring endomorphism `σ`:
`det M_σ(g₁, …, g_m) ≠ 0` iff `g₁, …, g_m` are linearly independent over the fixed field
`L^σ = {u : σ u = u}`. -/
theorem lemma_6_4 {L : Type*} [Field L] (σ : L →+* L) {m : ℕ} (g : Fin m → L) :
    (casoratiMatrix σ g).det ≠ 0 ↔
      ∀ c : Fin m → L, (∀ j, σ (c j) = c j) → ∑ j, c j * g j = 0 → ∀ j, c j = 0 := by sorry

end HasseHSG.Generator
