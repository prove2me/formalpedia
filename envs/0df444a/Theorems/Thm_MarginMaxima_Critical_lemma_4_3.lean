-- Prove2me | Theorems.Thm_MarginMaxima_Critical_lemma_4_3
-- name    : MarginMaxima.Critical.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:02:50.939195+00:00
-- url     : https://prove2.me/theorems/60f62010-7b15-4c44-943b-9d3211d6df46
-- title:
--   Lemma 4.3 — block to shattering: $\ge np/18$ documents realized by $r'=\lceil4(c_1+1)np/M_0\rceil+1$ block or null heads
-- statement:
--   Let $c_1=\ln1600$, $np\ge64$ (with $n=|C|$, $p=M_0/M$, $M_0\le M$ an integer), and let the block system be $(M,j)$-regular with $j=\lceil c_12^{M_0-1}/\pi_0\rceil$. With $r'=\lceil4(c_1+1)np/M_0\rceil+1$, a set $Y$ of at least $np/18$ documents is realized by $r'$ heads, all of them block heads or the null head:
--   $$\exists\,Y\subseteq C,\quad |Y|\ge np/18,\quad Y\ \text{realized by } r' \text{ heads from } \{u_B\}\cup\{-\kappa h_0\}.$$
--
--   Differences from the source:
--   - encoding: a block system: Hilbert space ℒ ⊥ h₀, documents ξ_y + κh₀, heads ℓ_B − κh₀ → BlockSystem L C β g s κ with L a complete real inner product space, blocks indexed by β, and scores ⟨ℓ, ξ_y⟩ − κ²; reason: ⟨ℓ − κh₀, ξ + κh₀⟩ = ⟨ℓ, ξ⟩ − κ² since ℓ, ξ ⊥ h₀ and ∥h₀∥ = 1; the same systems
--   - encoding: n = |C|, M₀ ≤ M an integer, p = M₀/M → Fintype.card C, M M0 : ℕ with M0 ≤ M, p written (M0 : ℝ)/M; reason: the §4 setting (p. 8)
--   - encoding: realized by r′ heads, all of them block heads or the null head → RealizesWith Y r′ BlockOrNull: every head's ℒ-part is 0 (the null head −κh₀) or ℓ_B for a block B; reason: literal; the null head has ℒ-part 0
--   - encoding: j = ⌈c₁2^{M₀−1}/π₀⌉, r′ = ⌈4(c₁+1)np/M₀⌉ + 1 → Nat.ceil of the same real expressions, c₁ = Real.log 1600; reason: literal
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 8, Lemma 4.3

import Mathlib
import Definitions.Def_MarginMaxima_Critical_BlockSystem

namespace MarginMaxima.Critical

theorem lemma_4_3 {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L]
    {C β : Type} [Fintype C] [DecidableEq C] [Fintype β] {g s κ : ℝ}
    (S : BlockSystem L C β g s κ) (M M0 : ℕ) (hM0 : M0 ≤ M)
    (hnp : 64 ≤ (Fintype.card C : ℝ) * ((M0 : ℝ) / M))
    (hreg : S.IsRegular M ⌈Real.log 1600 * 2 ^ (M0 - 1) / pi0 M M0 ((M0 : ℝ) / M)⌉₊) :
    ∃ Y : Finset C, (Fintype.card C : ℝ) * ((M0 : ℝ) / M) / 18 ≤ Y.card ∧
      S.RealizesWith Y
        (⌈4 * (Real.log 1600 + 1) * ((Fintype.card C : ℝ) * ((M0 : ℝ) / M)) / M0⌉₊ + 1)
        S.BlockOrNull := by sorry

end MarginMaxima.Critical
