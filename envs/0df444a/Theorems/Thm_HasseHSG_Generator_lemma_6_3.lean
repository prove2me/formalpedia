-- Prove2me | Theorems.Thm_HasseHSG_Generator_lemma_6_3
-- name    : HasseHSG.Generator.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:36:33.299022+00:00
-- url     : https://prove2.me/theorems/c5c8e756-8b35-4096-b477-2c9f6a01c5bc
-- title:
--   Lemma 6.3 — $M_{D_{q,d}}=\Lambda_m M_{\sigma_q}$ with $\Lambda_m$ lower triangular and $\det\Lambda_m\neq0$
-- statement:
--   Throughout, $F$ is an arbitrary field, $a_1,\dots,a_n\in F$ are distinct and nonzero, and $q$ is transcendental over $F$ (the standing assumptions of §5.3). Let $L=\operatorname{Frac}(F(q)(t)[x])$ and $m\in\mathbb N$.
--
--   The $D_{q,d}$-Wronskian matrix of Eq. (16) factors through the Casoratian of Eq. (17). There is an $m\times m$ matrix $\Lambda_m$ over $L$ such that:
--
--   1. $\Lambda_m$ is lower triangular;
--   2. $\det\Lambda_m\ne0$;
--   3. for all $g_1,\dots,g_m\in L$,
--   $$M_{D_{q,d}}(g_1,\dots,g_m)=\Lambda_m\,M_{\sigma_q}(g_1,\dots,g_m).$$
--
--   Consequently $W_{D_{q,d}}(g)\ne0$ if and only if $\det M_{\sigma_q}(g)\ne0$. This reduces Theorem 6.2 to the Casoratian criterion.
--
--   Differences from the source:
--   - reading: a lower-triangular matrix Λ_m (indexed by m only) → one Λ for all g₁, …, g_m ∈ L (∃ Λ, ∀ g); reason: the notation Λ_m and the proof's operator identity D^r = Σ_j λ_{r,j} σ_q^j give a Λ independent of g; this is the stronger of the two readings
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 28, Lemma 6.3 (proof pp. 28–29)

import Mathlib
import Definitions.Def_HasseHSG_Generator_QDifference
import Definitions.Def_HasseHSG_Generator_Wronskian

namespace HasseHSG.Generator

/-- Lemma 6.3 (p. 28): `M_{D_{q,d}} = Λ_m · M_{σ_q}` with `Λ_m` lower triangular, `det Λ_m ≠ 0`,
and `Λ_m` the same for all `g₁, …, g_m ∈ L`. -/
theorem lemma_6_3 {F : Type*} [Field F] {n d : ℕ} (a : Fin n → F)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) (m : ℕ) :
    ∃ Λ : Matrix (Fin m) (Fin m) (LField F n),
      (∀ i j : Fin m, i < j → Λ i j = 0) ∧ Λ.det ≠ 0 ∧
      ∀ g : Fin m → LField F n, wronskianMatrix a d g = Λ * qCasoratiMatrix a g := by sorry

end HasseHSG.Generator
