-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_kiefer_wolfowitz
-- name    : KhachiyanRound.BCD.kiefer_wolfowitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:12.96413+00:00
-- url     : https://prove2.me/theorems/4ba71869-59b9-4d1e-b37a-e14acc3037ba
-- title:
--   (2.9), p. 309 — Kiefer–Wolfowitz: wⱼ(p*) ≤ n at every maximizer p* of (2.3)
-- statement:
--   Let $a_1,\dots,a_m \in \mathbb{R}^n$ have affine hull $\mathbb{R}^n$ (2.2), and let $p^* \in S_F$ maximize $F(p) = \ln\det A(p)$ over $S_F$. Then the Kiefer–Wolfowitz optimality conditions hold:
--   $$w_j(p^*) = a_j^{\mathsf T}[A(p^*)]^{-1}a_j \le n, \qquad j = 1,\dots,m.$$
--
--   These are the exact optimality conditions of which (2.10) is the $\varepsilon$-relaxation; together with Lemma 1 they give complementary slackness (2.11).
--
--   **Formalization Note** A maximizer over $S$ lies in $S_F$ under (2.2), so the maximization is stated over $S_F$ (Lean's `Real.log 0 = 0` makes a maximization over all of $S$ meaningless). The standing assumptions (2.1) and $n\ge 2$ of §2 are not needed and are dropped.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 309, (2.9)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem kiefer_wolfowitz {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ)
    (hfull : affineSpan ℝ (Set.range a) = ⊤)
    (pstar : ι → ℝ) (hpstar : pstar ∈ SF a) (hmax : ∀ q ∈ SF a, F a q ≤ F a pstar) :
    ∀ j, w a pstar j ≤ (n : ℝ) := by sorry
end KhachiyanRound.BCD
