-- Prove2me | Theorems.Thm_IntMul_HvdH_Ref_mkParams_step
-- name    : IntMul.HvdH.Ref.mkParams_step
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T19:14:16.119977+00:00
-- url     : https://prove2.me/theorems/65719875-ff1b-47a6-a49a-fa1cff86b788
-- title:
--   One Harvey–van der Hoeven step: exact product and digit bounds
-- statement:
--   Fix $K \ge 1$ and put $C = 64K^2\,(256K^2)!$. For every $N \ge 2^{2^{KC+4}}$ and all natural numbers $x, y < 2^N$, let $q = \mathrm{mkParams}(K,N)$ with chunk size $b$, $L$ chunks and target box size $2^{\log T}$. Then one step of the list-level Harvey–van der Hoeven multiplication is exact,
--   $$\mathrm{refStep}(q, x, y) = x\,y,$$
--   and every digit $c$ read back by the inverse Agarwal–Cooley map (the input of the final evaluation at $2^b$) is a linear convolution coefficient of the base-$2^b$ digits of $x$ and $y$, so
--   $$0 \le c < 2^{2b + \log T}.$$
--   The digit bound lets the machine evaluate with nonnegative digits only.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), Proposition 5.4 and §5.3

import Definitions.Def_IntMul_HvdH_MachineRef

namespace IntMul.HvdH.Ref
theorem mkParams_step (K : ℕ) (hK : 1 ≤ K) (N : ℕ)
    (hN : 2 ^ 2 ^ (K * (64 * K ^ 2 * (256 * K ^ 2).factorial) + 4) ≤ N)
    (x y : ℕ) (hx : x < 2 ^ N) (hy : y < 2 ^ N) :
    refStep (mkParams K N) x y = x * y ∧
    ∀ c ∈ crtOut (mkParams K N).s (2 * (mkParams K N).L - 1)
      (exactConvL (mkParams K N) (crtIn (mkParams K N).s (chunksL (mkParams K N).b (mkParams K N).L x))
        (crtIn (mkParams K N).s (chunksL (mkParams K N).b (mkParams K N).L y))),
      0 ≤ c ∧ c < 2 ^ (2 * (mkParams K N).b + (mkParams K N).logT) := by sorry
end IntMul.HvdH.Ref
