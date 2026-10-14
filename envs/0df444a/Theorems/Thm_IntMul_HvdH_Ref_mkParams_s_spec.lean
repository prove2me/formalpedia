-- Prove2me | Theorems.Thm_IntMul_HvdH_Ref_mkParams_s_spec
-- name    : IntMul.HvdH.Ref.mkParams_s_spec
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T21:19:32.750257+00:00
-- url     : https://prove2.me/theorems/99a8acb9-130d-4b86-a3ff-1dc63875cd21
-- title:
--   Source lengths of mkParams are pairwise coprime and sit in the window
-- statement:
--   Fix $K \ge 1$ and put $C = 64K^2\,(256K^2)!$. For every $N \ge 2^{2^{KC+4}}$, the source lengths $s_0,\dots,s_{K-1}$ of $q = \mathrm{mkParams}(K,N)$ form a list of length $K$ of pairwise coprime positive integers, and each satisfies
--   $$\frac{4K-2}{4K}\,2^{t_i} < s_i \le \frac{4K-1}{4K}\,2^{t_i},$$
--   where $2^{t_i}$ is the corresponding target length.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), Lemma 5.1 and §5.3

import Definitions.Def_IntMul_HvdH_MachineRef

namespace IntMul.HvdH.Ref
theorem mkParams_s_spec (K : ℕ) (hK : 1 ≤ K) (N : ℕ)
    (hN : 2 ^ 2 ^ (K * (64 * K ^ 2 * (256 * K ^ 2).factorial) + 4) ≤ N) :
    (mkParams K N).s.length = K ∧ (mkParams K N).s.Pairwise Nat.Coprime ∧
    (∀ x ∈ (mkParams K N).s, 0 < x) ∧
    ∀ i < K, (4 * K - 2) * 2 ^ (mkParams K N).te i < 4 * K * (mkParams K N).s.getD i 1 ∧
      4 * K * (mkParams K N).s.getD i 1 ≤ (4 * K - 1) * 2 ^ (mkParams K N).te i := by sorry
end IntMul.HvdH.Ref
