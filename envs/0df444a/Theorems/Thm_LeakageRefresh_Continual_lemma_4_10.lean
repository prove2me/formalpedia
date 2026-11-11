-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_lemma_4_10
-- name    : LeakageRefresh.Continual.lemma_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:09:08.511929+00:00
-- url     : https://prove2.me/theorems/51ea8e41-42e6-49b4-963c-bb5731ba1d35
-- title:
--   Lemma 4.10 — invertible versus unrestricted binary matrices: $\Pr[A_0\text{ invertible}]=\prod_{j=1}^n(1-2^{-j})>1/4$ and $\mathbb E_Mg\le4\,\mathbb E_{A_0}g$
-- statement:
--   Let $n\ge2$, let $A_0$ be uniform on $\mathbb F_2^{n\times n}$ and $M$ uniform on $\mathrm{InvMatr}^n_2$. Then
--   $$\Pr[A_0\text{ is invertible}]=\prod_{j=1}^n\big(1-2^{-j}\big)>\frac14, \tag{4.44}$$
--   and for every nonnegative function $g$ on all binary $n\times n$ matrices,
--   $$\mathbb E_M[g(M)]\le4\,\mathbb E_{A_0}[g(A_0)]. \tag{4.45}$$
--
--   Differences from the source:
--   - encoding: $\Pr[A_0\text{ is invertible}]$, $\mathbb E_M$, $\mathbb E_{A_0}$ → the count of `IsUnit` matrices divided by $|\mathbb F_2^{n\times n}|$; `avg` over `InvMatr n` and over all matrices; reason: uniform probabilities and expectations on finite sets
--   - encoding: the chain $\Pr[\cdot]=\prod_{j=1}^n(1-2^{-j})>1/4$ → two conjuncts: the identity, and $1/4<\prod_{j\in[1,n]}(1-2^{-j})$; reason: a chain is the conjunction of its links
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 37, Lemma 4.10

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_Tables

namespace LeakageRefresh.Continual

open Classical in
/-- **Lemma 4.10 (Comparison with unrestricted matrices).** For `A₀` uniform on `F₂^{n×n}` and
`M` uniform on `InvMatrⁿ₂`: (4.44) `P[A₀ is invertible] = ∏_{j=1}^{n} (1 − 2^{−j}) > 1/4`, and
(4.45) `E_M[g(M)] ≤ 4 E_{A₀}[g(A₀)]` for every nonnegative `g` on all binary `n × n` matrices. -/
theorem lemma_4_10 (n : ℕ) (hn : 2 ≤ n) :
    ((Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) (ZMod 2) => IsUnit A)).card : ℝ) /
        (Fintype.card (Matrix (Fin n) (Fin n) (ZMod 2)) : ℝ) =
      ∏ j ∈ Finset.Icc 1 n, (1 - (2 : ℝ) ^ (-(j : ℤ))) ∧
    1 / 4 < ∏ j ∈ Finset.Icc 1 n, (1 - (2 : ℝ) ^ (-(j : ℤ))) ∧
    ∀ g : Matrix (Fin n) (Fin n) (ZMod 2) → ℝ, (∀ A, 0 ≤ g A) →
      avg (fun M : InvMatr n => g (M : Matrix (Fin n) (Fin n) (ZMod 2))) ≤ 4 * avg g := by sorry

end LeakageRefresh.Continual
