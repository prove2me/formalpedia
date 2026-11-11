-- Prove2me | Theorems.Thm_HasseHSG_Generator_theorem_6_2
-- name    : HasseHSG.Generator.theorem_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:36:41.500099+00:00
-- url     : https://prove2.me/theorems/9be41796-dc45-40a7-8216-585421536e1f
-- title:
--   Theorem 6.2 — $W_{D_{q,d}}(g_1,\dots,g_m)\neq0$ iff $g_1,\dots,g_m$ are $F(q)$-linearly independent
-- statement:
--   Throughout, $F$ is an arbitrary field, $a_1,\dots,a_n\in F$ are distinct and nonzero, and $q$ is transcendental over $F$ (the standing assumptions of §5.3). Let $L=\operatorname{Frac}(F(q)(t)[x_1,\dots,x_n])$ with the operator $D_{q,d}=Q_d(t)(\sigma_q-\mathrm{id})/((q-1)t)$.
--
--   For $g_1,\dots,g_m\in L$,
--
--   $$W_{D_{q,d}}(g_1,\dots,g_m)\neq0\iff g_1,\dots,g_m\ \text{are}\ F(q)\text{-linearly independent}.$$
--
--   This is the characteristic-free replacement for the classical Wronskian criterion. In characteristic $p$ the derivation-based Wronskian fails, for example on $x_1^p,x_2^p$.
--
--   **Formalization Note.** $F(q)$-linear independence is stated through the inclusion $F(q)\subseteq L$: if $\sum_j c_jg_j=0$ with $c_j\in F(q)$, then every $c_j=0$.
--
--   Differences from the source:
--   - encoding: F(q)-linear independence in L → ∀ c : Fin m → F(q), Σ embFqL (c j) * g j = 0 → c = 0; reason: the definition, with F(q) acting on L through its inclusion
--   - encoding: q transcendental over F; F(q), F(q)(t) → RatFunc F with q = X; RatFunc (RatFunc F) with t = X; reason: Lean convention; F(q) is the rational function field in a transcendental
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 28, Theorem 6.2 (proof p. 30)

import Mathlib
import Definitions.Def_HasseHSG_Generator_QDifference
import Definitions.Def_HasseHSG_Generator_Wronskian

namespace HasseHSG.Generator

/-- Theorem 6.2 (p. 28): `W_{D_{q,d}}(g₁, …, g_m) ≠ 0` iff `g₁, …, g_m ∈ L` are `F(q)`-linearly
independent. -/
theorem theorem_6_2 {F : Type*} [Field F] {n d m : ℕ} (a : Fin n → F)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) (g : Fin m → LField F n) :
    wronskian a d g ≠ 0 ↔
      ∀ c : Fin m → Fq F, ∑ j, embFqL (c j) * g j = 0 → ∀ j, c j = 0 := by sorry

end HasseHSG.Generator
