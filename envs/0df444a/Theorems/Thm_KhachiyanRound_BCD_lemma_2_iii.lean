-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_lemma_2_iii
-- name    : KhachiyanRound.BCD.lemma_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:06.635803+00:00
-- url     : https://prove2.me/theorems/1c1dd646-39df-4722-af59-7ea1d64ae31c
-- title:
--   Lemma 2(iii), p. 310 — (2.10) implies vol(√((1 + ε)n) E_p) ≤ (1 + ε)^{n/2} vol E_*(𝒜)
-- statement:
--   Let $\mathcal A = \{a_1,\dots,a_m\} \subset \mathbb{R}^n$ be centrally symmetric (2.1) and full-dimensional (2.2), and let $p \in S_F$ satisfy $w_j(p) \le (1+\varepsilon)n$ for all $j$, with $\varepsilon \ge 0$. Let $E_*(\mathcal A)$ be the minimum-volume ellipsoid circumscribed about $\mathcal A$. Then
--   $$\operatorname{vol}\big(\sqrt{(1+\varepsilon)n}\,E_p\big) \le (1+\varepsilon)^{n/2}\operatorname{vol} E_*(\mathcal A).$$
--
--   The covering ellipsoid $\sqrt{(1+\varepsilon)n}\,E_p$ of Lemma 2(ii) is therefore also a near-minimum-volume one, which is how the method approximates the Löwner ellipsoid (Theorem 3).
--
--   **Formalization Note** $E_*(\mathcal A)$ is any pair $(A,b)$ satisfying the published `ConvexOptimization.IsLownerJohn A b 𝒜`, with ellipsoid $\{v \mid \|Av+b\| \le 1\}$; such a pair exists by `ConvexOptimization.lowner_john_exists`, so the universal quantifier is not vacuous. Volumes are Lebesgue measure in `ℝ≥0∞`.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 310, Lemma 2(iii)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_ConvexOptimization_ellipsoidBody
import Definitions.Def_ConvexOptimization_IsLownerJohn
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem lemma_2_iii {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ)
    (hsymm : IsCentrallySymmetric a) (hfull : affineSpan ℝ (Set.range a) = ⊤)
    (p : ι → ℝ) (hp : p ∈ SF a) (ε : ℝ) (hε : 0 ≤ ε) (hopt : IsRelaxedOpt a p ε) :
    ∀ (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ),
      ConvexOptimization.IsLownerJohn A b (Set.range a) →
        MeasureTheory.volume
            (Real.sqrt ((1 + ε) * (n : ℝ)) • LinearOptimization.ellipsoid 0 (momentMatrix a p)) ≤
          ENNReal.ofReal ((1 + ε) ^ ((n : ℝ) / 2)) *
            MeasureTheory.volume (ConvexOptimization.ellipsoidBody A b) := by sorry

end KhachiyanRound.BCD
