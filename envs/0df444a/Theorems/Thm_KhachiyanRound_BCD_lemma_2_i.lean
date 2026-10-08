-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_lemma_2_i
-- name    : KhachiyanRound.BCD.lemma_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:29.629359+00:00
-- url     : https://prove2.me/theorems/0f73b481-49c7-4d6f-8f0e-5515e9ecbe4f
-- title:
--   Lemma 2(i), p. 310 — (2.10) implies 0 ≤ F* − F(p) ≤ n ln(1 + ε)
-- statement:
--   Let $\mathcal A = \{a_1,\dots,a_m\} \subset \mathbb{R}^n$ be centrally symmetric (2.1) with affine hull $\mathbb{R}^n$ (2.2). Suppose $p \in S_F$ satisfies the $\varepsilon$-relaxed optimality conditions $w_j(p) \le (1+\varepsilon)n$ for all $j$, with some $\varepsilon \ge 0$. Then
--   $$0 \le F^* - F(p) \le n\ln(1+\varepsilon),$$
--   where $F^* = \sup_{q\in S_F} F(q)$ is the optimal value of the D-optimal design problem (2.3).
--
--   The relaxed conditions thus certify near-optimality of $p$ in objective value; this is the bound (2.22) used to count BCD iterations.
--
--   **Formalization Note** The standing assumption $n \ge 2$ of §2 is not used by Lemma 2 and is dropped. $F^*$ is the supremum over $S_F$ (on the page, the maximum over $S$, which is the same number).
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 310, Lemma 2(i)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem lemma_2_i {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ)
    (hsymm : IsCentrallySymmetric a) (hfull : affineSpan ℝ (Set.range a) = ⊤)
    (p : ι → ℝ) (hp : p ∈ SF a) (ε : ℝ) (hε : 0 ≤ ε) (hopt : IsRelaxedOpt a p ε) :
    0 ≤ Fstar a - F a p ∧ Fstar a - F a p ≤ (n : ℝ) * Real.log (1 + ε) := by sorry
end KhachiyanRound.BCD
