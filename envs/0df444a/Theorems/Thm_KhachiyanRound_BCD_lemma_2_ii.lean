-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_lemma_2_ii
-- name    : KhachiyanRound.BCD.lemma_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:51.241335+00:00
-- url     : https://prove2.me/theorems/c89da0ef-4f22-429f-a12f-568871781838
-- title:
--   Lemma 2(ii), p. 310 — (2.10) implies E_p ⊆ conv.hull(𝒜) ⊆ √((1 + ε)n) E_p
-- statement:
--   Let $\mathcal A = \{a_1,\dots,a_m\} \subset \mathbb{R}^n$ be centrally symmetric (2.1) with affine hull $\mathbb{R}^n$ (2.2). Suppose $p \in S_F$ satisfies $w_j(p) \le (1+\varepsilon)n$ for all $j$, with some $\varepsilon \ge 0$. Let
--   $$E_p = \{x \in \mathbb{R}^n \mid x^{\mathsf T}[A(p)]^{-1}x \le 1\}.$$
--   Then
--   $$E_p \subseteq \operatorname{conv}(\mathcal A) \subseteq \sqrt{(1+\varepsilon)n}\;E_p .$$
--
--   So any point satisfying the relaxed conditions yields a $\sqrt{(1+\varepsilon)n}$-rounding of the symmetric polytope $\operatorname{conv}(\mathcal A)$, computable from $A(p)$ alone. This is the geometric content of Theorem 1.
--
--   **Formalization Note** $E_p$ is the published `LinearOptimization.ellipsoid 0 (A p)` and $\sqrt c\,E_p$ is the pointwise scalar multiple (both centred at the origin). The standing assumption $n\ge2$ is not used and is dropped.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 310, Lemma 2(ii)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem lemma_2_ii {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ)
    (hsymm : IsCentrallySymmetric a) (hfull : affineSpan ℝ (Set.range a) = ⊤)
    (p : ι → ℝ) (hp : p ∈ SF a) (ε : ℝ) (hε : 0 ≤ ε) (hopt : IsRelaxedOpt a p ε) :
    LinearOptimization.ellipsoid 0 (momentMatrix a p) ⊆ convexHull ℝ (Set.range a) ∧
      convexHull ℝ (Set.range a) ⊆
        Real.sqrt ((1 + ε) * (n : ℝ)) • LinearOptimization.ellipsoid 0 (momentMatrix a p) := by sorry
end KhachiyanRound.BCD
