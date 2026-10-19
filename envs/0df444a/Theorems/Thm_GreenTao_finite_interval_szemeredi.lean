-- Prove2me | Theorems.Thm_GreenTao_finite_interval_szemeredi
-- name    : GreenTao.finite_interval_szemeredi
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T20:36:19.851263+00:00
-- url     : https://prove2.me/theorems/906f339a-ac53-4b07-9a10-781201b1f53f
-- title:
--   Finite-interval Szemerédi input for Varnavides counting
-- statement:
--   Fix an integer $k\ge3$ and a real number $\delta>0$. There is an integer $L\ge k$ such that every set $S\subseteq\{0,\ldots,L-1\}$ with $|S|\ge\delta L$ contains an arithmetic progression of length $k$ and positive common difference:
--
--   $$\exists a,d\in\mathbb N,\quad d>0,\quad a+(k-1)d<L,\quad a+jd\in S\  (0\le j<k).$$
--
--   This finite-interval existence statement is the qualitative input used by the affine-window proof of Varnavides counting. The length $L$ depends only on $k$ and $\delta$. It is an interval form of Szemerédi’s theorem, expressed with zero-based indices for pulling sets back along affine maps.
-- source:
--   E. Szemerédi, On sets of integers containing no k elements in arithmetic progression, Acta Arith. 27 (1975). Finite-interval form of the qualitative theorem; compare Green–Tao, https://arxiv.org/html/math/0404188v6, §2 Proposition 2.1 and the Varnavides discussion after Proposition 2.3. The proof imports the existing platform theorem Erdos142.erdos_139_szemeredi (7653083f-b258-4a2c-a86d-f689b72bf0ff) rather than reproving it.

import Mathlib

theorem GreenTao.finite_interval_szemeredi (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℕ, k ≤ L ∧
      ∀ S : Finset ℕ, S ⊆ Finset.range L → δ * (L : ℝ) ≤ (S.card : ℝ) →
        ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < L ∧
          ∀ j < k, a + j * d ∈ S := by sorry
