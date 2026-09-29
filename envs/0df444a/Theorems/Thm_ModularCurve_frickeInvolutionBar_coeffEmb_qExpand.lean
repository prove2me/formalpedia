-- Prove2me | Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
-- name    : ModularCurve.frickeInvolutionBar_coeffEmb_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/05415233-8d55-57c1-b642-f13d86be225b
-- title:
--   Fricke involution over ℚ̄ exchanges j(qᵃ) and j(qᵇ)
-- statement:
--   Let $N$ be a positive natural number and suppose the canonically chosen automorphism `frickeInvolutionFull N` of the modular function field $F_N =$ `modularFunctionFieldFull N` — the intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ generated over $\mathbb{Q}$ by `divisorExpansions N` — satisfies `IsFrickeAutFull N`, i.e. for every factorisation $a'b' = N$ into positive naturals it carries the element $j(q^{a'})$, namely the image of the $q$-expansion `jq` $= q^{-1}\cdot$`jNumQ` under the substitution $q \mapsto q^{a'}$ (`qExpand ℚ a'`), to $j(q^{b'})$; membership of these elements in $F_N$ is provided by `jqd_mem_full`. Let $a, b$ be positive naturals with $a \cdot b = N$. Then the base-changed automorphism `frickeInvolutionBar N`, the image of `frickeInvolutionFull N` under `geomAut` and hence an $\bar{\mathbb{Q}}$-algebra automorphism of `modularFunctionFieldBar N` $=$ `laurentBaseChange (AlgebraicClosure ℚ)`$F_N$ inside $\bar{\mathbb{Q}}((q))$, sends the element with underlying series the coefficientwise image `coeffEmb` of $j(q^{a})$ along $\mathbb{Q} \to \bar{\mathbb{Q}}$ to the element with underlying series the coefficientwise image of $j(q^{b})$.
--
--   This transports the defining exchange property of the Fricke involution $w_N$ on the function field of $X_0(N)$ over $\mathbb{Q}$ to the geometric function field over $\bar{\mathbb{Q}}$, where the geometric theory of $X_0(N)$, its cusps and its cuspidal divisor classes is developed. It is used throughout that development, for instance in identifying the $w_N$-image of the generator $j(q^{\,\cdot})$ and in the analysis of charts and centredness conditions on the geometric curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand.lean

import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.frickeInvolutionBar_coeffEmb_qExpand (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (a b : ℕ) (hab : a * b = N) [NeZero a] [NeZero b] : frickeInvolutionBar N ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro b hab))⟩ = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro_left a hab))⟩ := by sorry
