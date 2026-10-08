-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_lemma_1
-- name    : KhachiyanRound.BCD.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:41.376645+00:00
-- url     : https://prove2.me/theorems/82074033-981c-4ea5-88df-06144ef754cb
-- title:
--   Lemma 1, p. 310 — Σⱼ pⱼwⱼ(p) = n for every p ∈ S_F
-- statement:
--   Let $a_1,\dots,a_m \in \mathbb{R}^n$ and let $p$ be a point of the unit simplex with $\det A(p) > 0$, where $A(p) = \sum_i p_i a_i a_i^{\mathsf T}$. With $w_j(p) = a_j^{\mathsf T}[A(p)]^{-1}a_j$,
--   $$\sum_{j=1}^m p_j\, w_j(p) = n.$$
--
--   The $p$-weighted average of the leverages is exactly the dimension. In particular $\max_j w_j(p) \ge n$, so the accuracy $\varepsilon(p)$ is nonnegative, and the identity is the complementary-slackness ingredient of the Kiefer–Wolfowitz conditions.
--
--   **Formalization Note** The page states the lemma in §2, whose standing assumptions are central symmetry (2.1), full dimension (2.2) and $n \ge 2$; the lemma uses none of them, and the Lean statement drops all three.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 310, Lemma 1

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem lemma_1 {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ)
    (p : ι → ℝ) (hp : p ∈ SF a) :
    ∑ j, p j * w a p j = (n : ℝ) := by sorry
end KhachiyanRound.BCD
