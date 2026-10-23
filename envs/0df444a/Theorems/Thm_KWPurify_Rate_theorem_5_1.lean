-- Prove2me | Theorems.Thm_KWPurify_Rate_theorem_5_1
-- name    : KWPurify.Rate.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:15.213896+00:00
-- url     : https://prove2.me/theorems/8a7eacd4-5fdb-4565-a74f-967e41e4cbc1
-- title:
--   Theorem 5.1 (all-qubit half, (31) corrected) — $F^{\max}_{\mathrm{all}}(N,M) = \sum_s w_N(s) f_{\mathrm{all}}(M,\beta,s)$, and the supremum is attained
-- statement:
--   Let $\beta > 0$ and $\lambda = \tanh\beta$, so that $0 < \lambda < 1$. For all $N, M \in \mathbb N$ the optimal all-qubit fidelity of a purifier from $N$ noisy qubits to $M$ qubits is
--   $$F^{\max}_{\mathrm{all}}(N,M) = \sum_{s\in I[N]} w_N(s)\, f_{\mathrm{all}}(M,\beta,s),$$
--   with the weights $w_N(s)$ of eq. (14) and the closed form $f_{\mathrm{all}}$ of Proposition 4.2. Moreover the supremum defining $F^{\max}_{\mathrm{all}}(N,M)$ is attained by some channel $T$.
--
--   The supremum ranges over all quantum channels from $N$ to $M$ qubits; the theorem says that the optimal purifier of the paper achieves it, reducing the variational problem to an explicit finite sum.
--
--   **Formalization Note** Corrected statement: (31) prints $f_{\mathrm{one}}$ in the summand, which is a misprint for $f_{\mathrm{all}}$; $f_{\mathrm{all}}$ is the corrected closed form (see Proposition 4.2). Spins are encoded by $k = N/2 - s$, $2s = N - 2k$, and the sum runs over $k = 0,\dots,\lfloor N/2\rfloor$. The one-qubit half of Theorem 5.1 is not part of this statement.
-- source:
--   Keyl & Werner, The Rate of Optimal Purification procedures, arXiv:quant-ph/9910124v1, p. 15, Theorem 5.1 (all-qubit part) with eq. (31) (corrected), proof pp. 15–17

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_KWPurify_Rate_Model
import Definitions.Def_KWPurify_Rate_Blocks

namespace KWPurify.Rate
theorem theorem_5_1 (β : ℝ) (hβ : 0 < β) (N M : ℕ) :
    maxAllFidelity (Real.tanh β) N M =
      ∑ k ∈ Finset.range (N / 2 + 1), spinWeight β N k * fAll M β (N - 2 * k) ∧
    ∃ T : QAlgorithms.Superop (Fin N → Fin 2) (Fin M → Fin 2), QAlgorithms.IsChannel T ∧
      allFidelity (Real.tanh β) T = maxAllFidelity (Real.tanh β) N M := by sorry
end KWPurify.Rate
