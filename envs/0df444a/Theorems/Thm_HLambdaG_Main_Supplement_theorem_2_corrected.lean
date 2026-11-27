-- Prove2me | Theorems.Thm_HLambdaG_Main_Supplement_theorem_2_corrected
-- name    : HLambdaG.Main.Supplement.theorem_2_corrected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:02:24.243263+00:00
-- url     : https://prove2.me/theorems/0910c464-ca96-4c6b-af1f-13f25e01c762
-- title:
--   Theorem 2, p. 640 (corrected: (17) summed from k = n + 1) — in the setting of §1.1, (17) is equivalent to (14)
-- statement:
--   Consider the setting of §1.1. Customers $k\ge1$ have nonnegative, nondecreasing, bounded inputs $F_k$ with $\sum_kF_k(t)<\infty$. The epochs satisfy $0=T_0\le T_1\le\cdots$ and $T_k\to\infty$. The cumulative input is $F(s,t)=\sum_{k=1}^{[s]}F_k(t)$ and the time change is $T_1(s)=T_{[s]}$. Then
--   $$
--   n^{-1}\sum_{k=n+1}^{\infty}F_k(T_n)\to0\quad(n\to\infty)
--   \qquad\Longleftrightarrow\qquad
--   s^{-1}\bigl[F(s,T_1(s-))-F(\infty,T_1(s-))\bigr]\to0\quad(s\to\infty).
--   $$
--   The left-hand side is condition (17). The right-hand side is condition (14) of §2.
--
--   Theorem 2 turns the general approximation condition (14), which enters Theorem 1, into a condition on the sequence data. Inputs of customers who have not yet arrived at $T_n$ must contribute $o(n)$.
--
--   **Formalization Note** The printed (17) sums from $k=n$. With that lower index the theorem is false. Take $T_k=k$ and $F_k(t)=k\cdot1\{t\ge k\}$. Then (14) holds identically, since every bracket is $0$, but $n^{-1}\sum_{k\ge n}F_k(T_n)=n^{-1}F_n(n)=1$. The proof on p. 640 computes, for $n<s<n+1$, exactly $n^{-1}\sum_{k=n+1}^\infty F_k(T_n)=[s]^{-1}[F(\infty,T_1(s-))-F(s,T_1(s-))]$, and at $s=n$ the same sum shifted by one index. So the lower index $n+1$ is the intended one. The printed (17) implies the corrected one, because its terms are nonnegative. $T_1(s-)$ is the published left limit, and both directions of the equivalence are stated.
--
--   Differences from the source:
--
--   - correction: (17): n⁻¹ Σ_{k=n}^∞ F_k(T_n) → 0 → Cond17: n⁻¹ Σ_{k=n+1}^∞ F_k(T_n) → 0; reason: the sum computed in the proof of Theorem 2 on p. 640 starts at k = n + 1; with k = n the theorem is false (T_k = k, F_k(t) = k·1{t ≥ k}: (14) holds, printed (17) sum equals 1)
--   - encoding: s, t ∈ [0, ∞), customers k = 1, 2, … → s, t : ℝ≥0; customers indexed by ℕ with a dummy index 0 (F_0 = 0); reason: Lean convention; the index 0 carries no customer and every sum starts at k = 1, so no instance changes
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 640, Theorem 2 and its proof; condition (17) p. 640; https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_Discrete

open scoped NNReal

namespace HLambdaG.Main.Supplement

open Filter Topology

/-- Theorem 2, p. 640, with the lower summation index of (17) corrected to `n + 1`:
in the setting of §1.1, (17) is equivalent to (14) for `F(s, t) = Σ_{k ≤ [s]} F_k(t)` and
`T₁(s) = T_{[s]}`. -/
theorem theorem_2_corrected (D : DiscreteSetting) :
    D.Cond17 ↔ Cond14 D.input D.T1 := by sorry

end HLambdaG.Main.Supplement
