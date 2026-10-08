-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_exists_maximizer
-- name    : KhachiyanRound.BCD.exists_maximizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:15.053386+00:00
-- url     : https://prove2.me/theorems/db0684c8-a56a-4b51-a93f-9db5c2f950d1
-- title:
--   p. 309 — under (2.2) problem (2.3) has an optimal solution p* with F(p*) > −∞
-- statement:
--   Let $a_1,\dots,a_m \in \mathbb{R}^n$ have affine hull $\mathbb{R}^n$ (2.2). Then the D-optimal design problem (2.3),
--   $$\text{maximize } F(p) = \ln\det\Big(\sum_{i} p_i a_i a_i^{\mathsf T}\Big) \quad\text{over the unit simplex } S,$$
--   has an optimal solution $p^*$ with $F(p^*) > -\infty$: there is $p^* \in S_F$ with $F(q) \le F(p^*)$ for every $q \in S_F$, and then $F(p^*) = F^*$.
--
--   The existence of $p^*$ makes the optimal value $F^*$ of (2.3) a genuine maximum, which Lemma 2(i) and Lemma 3 compare against.
--
--   **Formalization Note** Since $F = -\infty$ off $S_F$ on the page, maximizing over $S$ and over $S_F$ is the same problem; the Lean statement maximizes over $S_F$, because Lean's `Real.log 0 = 0` would otherwise give singular weights a spurious value. The section's other standing assumptions, (2.1) and $n \ge 2$, are not needed and are dropped.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 309, paragraph after (2.4)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem exists_maximizer {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ)
    (hfull : affineSpan ℝ (Set.range a) = ⊤) :
    ∃ pstar ∈ SF a, (∀ q ∈ SF a, F a q ≤ F a pstar) ∧ F a pstar = Fstar a := by sorry
end KhachiyanRound.BCD
