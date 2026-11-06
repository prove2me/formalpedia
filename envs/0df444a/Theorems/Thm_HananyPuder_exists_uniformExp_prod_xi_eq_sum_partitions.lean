-- Prove2me | Theorems.Thm_HananyPuder_exists_uniformExp_prod_xi_eq_sum_partitions
-- name    : HananyPuder.exists_uniformExp_prod_xi_eq_sum_partitions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T22:12:46.692453+00:00
-- url     : https://prove2.me/theorems/e799e10c-bf53-4f9b-b7c5-2a38f54a4694
-- title:
--   Hanany–Puder, Remark 7.3 — E_unif[ξ₁^a₁⋯ξ_K^a_K] is eventually a sum over the partitions of a multiset
-- statement:
--   Let $a_1, \dots, a_K \ge 0$, and let $S$ be the multiset containing $t$ with multiplicity $a_t$ for $t = 1, \dots, K$, taken as a set of $a_1 + \dots + a_K$ labeled elements (`Σ t : Fin K, Fin (a t)`, the element $\langle t - 1, i\rangle$ carrying the value $t$). Then for all large enough $N$,
--   $$\mathbf E_{\mathrm{unif},N}[\xi_1^{a_1} \cdots \xi_K^{a_K}] = \sum_{\mathcal P \in \mathrm{Partitions}(S)} \prod_{A \in \mathcal P} \sum_{e \mid \gcd(A)} e^{|A| - 1},$$
--   where $\mathcal P$ runs over the partitions of the labeled set (`Finpartition`), $\gcd(A)$ is the greatest common divisor of the values in the block $A$, and $|A|$ is the number of elements of $A$. Here $\mathbf E_{\mathrm{unif},N}$ is the expectation over a uniform $\sigma \in \mathbf S_N$ and $\xi_t(\sigma)$ (`xi`) is the number of fixed points of $\sigma^t$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 31, the remark of Hanany–Puder cited in the proof of Lemma 10.2, which cites Hanany, L. and Puder, D., Word measures on symmetric groups, Int. Math. Res. Not. IMRN 2023 (2023) 9221–9297, https://doi.org/10.1093/imrn/rnac084 (arXiv:2009.00897v4), Remark 7.3

import Mathlib
import Definitions.Def_StrongConv

open StrongConv

namespace HananyPuder

theorem exists_uniformExp_prod_xi_eq_sum_partitions {K : ℕ} (a : Fin K → ℕ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      uniformExp (fun σ : Equiv.Perm (Fin N) =>
          ∏ t : Fin K, ((xi ((t : ℕ) + 1) σ : ℕ) : ℝ) ^ a t) =
        ∑ P : Finpartition (Finset.univ : Finset (Σ t : Fin K, Fin (a t))),
          ∏ A ∈ P.parts, ∑ e ∈ (A.gcd fun x => (x.1 : ℕ) + 1).divisors, (e : ℝ) ^ (A.card - 1) := by
  sorry

end HananyPuder
