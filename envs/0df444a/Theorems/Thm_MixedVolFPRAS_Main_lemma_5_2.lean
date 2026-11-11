-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_lemma_5_2
-- name    : MixedVolFPRAS.Main.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:32:01.830488+00:00
-- url     : https://prove2.me/theorems/7da8f3a8-88d9-47da-9135-4d3c393109d2
-- title:
--   Lemma 5.2 — t°ᵢ = Vₙ(K₋ᵢ, RB)/Vₙ(K) satisfies 1 ≤ t°ᵢ ≤ R/rᵢ and makes (t°₁K₁, …, t°ₙKₙ) 2-balanced
-- statement:
--   Let $K_1,\dots,K_n\subseteq\mathbb{R}^n$ be convex bodies with $r_iB_2^n\subseteq K_i\subseteq R_iB_2^n$, $r_i>0$, for each $i$; write $K=(K_1,\dots,K_n)$, $R=\max_iR_i$ and
--
--   $$t^\circ_i=\frac{V_n(K_{-i},RB_2^n)}{V_n(K)},\qquad i=1,\dots,n,$$
--
--   where $(K_{-i},RB_2^n)$ is $K$ with $K_i$ replaced by $RB_2^n$. Then $1\le t^\circ_i\le R/r_i$ for each $i$, and $(t^\circ_1K_1,\dots,t^\circ_nK_n)$ is $2$-balanced.
--
--   It shows that a balancing rescaling exists inside the box $\prod_i[1,R/r_i]$, which is what the convex program of Proposition 5.5 optimizes over.
--
--   Differences from the source:
--   - reading: $r_iB_2^n\subseteq K_i\subseteq R_iB_2^n$ → also $r_i>0$; reason: the radii come from Definition 1.1 ($0<r\le R$), and $R/r_i$ is meaningless at $r_i=0$.
--   - encoding: $R=\max_iR_i$ → `⨆ j, Rr j` (a supremum over the finite index set); reason: equal to the maximum for $n\ge1$.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 24, Lemma 5.2

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedVolume
import Definitions.Def_MixedVolFPRAS_Main_Balancing

open scoped Pointwise

namespace MixedVolFPRAS.Main

/-- **Lemma 5.2.** Let `K₁, …, Kₙ` be convex bodies with `rᵢ B₂ⁿ ⊆ Kᵢ ⊆ Rᵢ B₂ⁿ` (`rᵢ > 0`),
`R = maxᵢ Rᵢ` and `t°ᵢ = Vₙ(K_{−i}, R B₂ⁿ)/Vₙ(K)`. Then `1 ≤ t°ᵢ ≤ R/rᵢ` for each `i`, and
`(t°₁K₁, …, t°ₙKₙ)` is 2-balanced. -/
theorem lemma_5_2 {n : ℕ} (K : Fin n → Set (E n)) (r Rr : Fin n → ℝ)
    (hK : ∀ i, IsConvexBody (K i)) (hr : ∀ i, 0 < r i)
    (hin : ∀ i, r i • unitBall n ⊆ K i) (hout : ∀ i, K i ⊆ Rr i • unitBall n) :
    (∀ i, 1 ≤ mixedVolume (Function.update K i ((⨆ j, Rr j) • unitBall n)) / mixedVolume K ∧
        mixedVolume (Function.update K i ((⨆ j, Rr j) • unitBall n)) / mixedVolume K ≤
          (⨆ j, Rr j) / r i) ∧
      IsBalanced 2 (fun i =>
        (mixedVolume (Function.update K i ((⨆ j, Rr j) • unitBall n)) / mixedVolume K) • K i) := by sorry

end MixedVolFPRAS.Main
