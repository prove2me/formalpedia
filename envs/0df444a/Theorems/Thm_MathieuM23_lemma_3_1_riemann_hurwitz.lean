-- Prove2me | Theorems.Thm_MathieuM23_lemma_3_1_riemann_hurwitz
-- name    : MathieuM23.lemma_3_1_riemann_hurwitz
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T22:25:18.011363+00:00
-- url     : https://prove2.me/theorems/be48aab3-1e65-42a5-98d5-18ef778db6d3
-- title:
--   Lemma 3.1 — the Riemann–Hurwitz count giving genus $4$
-- statement:
--   The degree-23 cover $X_{\mathbb{C}}\to\mathbb{P}^1_{\mathbb{C}}$ with monodromy $(g_1,g_2,g_3)$ has genus $4$. Its ramification is read off from the cycle types. $g_1$ has cycle type $1^7 2^8$, so the fiber over the first branch point consists of eight points of ramification index $2$ and seven unramified points. $g_2$ and $g_3$ are $23$-cycles, so the other two fibers are totally ramified. The Riemann–Hurwitz formula then gives
--
--   $$2\cdot 4-2=23\,(2\cdot0-2)+\big[8(2-1)+(23-1)+(23-1)\big].$$
--
--   **Formalization Note** The curve $X_{\mathbb{C}}$ itself (obtained via the Riemann existence theorem) is not formalized. The milestone records the combinatorial content of Lemma 3.1: the cycle types of $g_1,g_2,g_3$ and the Riemann–Hurwitz identity. Here the contribution of $g$ is $\sum_{\text{cycles}}(\ell-1)$, the sum of the cycle lengths $\ell\ge2$ minus the number of such cycles.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 5, Lemma 3.1 and its proof

import Definitions.Def_MathieuM23_Group

namespace MathieuM23

theorem lemma_3_1_riemann_hurwitz :
    g₁.cycleType = Multiset.replicate 8 2 ∧ g₂.cycleType = {23} ∧ g₃.cycleType = {23} ∧
      (2 * 4 - 2 : ℤ) = 23 * (2 * 0 - 2) +
        (((g₁.cycleType.sum : ℤ) - g₁.cycleType.card) +
          ((g₂.cycleType.sum : ℤ) - g₂.cycleType.card) +
          ((g₃.cycleType.sum : ℤ) - g₃.cycleType.card)) := by sorry

end MathieuM23
