-- Prove2me | Theorems.Thm_IntMul_HvdH_Ref_refStep_mkParams
-- name    : IntMul.HvdH.Ref.refStep_mkParams
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T17:26:50.019212+00:00
-- url     : https://prove2.me/theorems/68053205-5b09-406d-9374-affa8084f774
-- title:
--   Correctness of one Harvey–van der Hoeven multiplication step
-- statement:
--   Fix a number of axes $K \ge 1$. There is $n_0$ such that for every $N \ge n_0$ and all natural numbers $x, y < 2^N$,
--   $$\mathrm{refStep}(\mathrm{mkParams}(K, N), x, y) = x\,y .$$
--   Here $\mathrm{refStep}$ is one recursive step of the Harvey–van der Hoeven integer multiplication algorithm as a computable list program: split into base-$2^b$ digits, Agarwal–Cooley reindexing onto a $K$-dimensional box with pairwise coprime odd side lengths, exact cyclic convolution via Gaussian resampling to a power-of-two box, a Bluestein DFT whose inner convolution is computed exactly in a Fermat ring, and a final rounding; $\mathrm{mkParams}(K,N)$ is the parameter choice for $N$-bit inputs. The statement says that, with these parameters and large inputs, all fixed-point errors stay below the rounding threshold so the step returns the exact product. It is the functional correctness half of Theorem 1.1 (the multitape machine implements refStep).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), Proposition 5.4 and §5.3

import Definitions.Def_IntMul_HvdH_MachineRef

namespace IntMul.HvdH.Ref
theorem refStep_mkParams (K : ℕ) (hK : 1 ≤ K) :
    ∃ n₀, ∀ N, n₀ ≤ N → ∀ x y : ℕ, x < 2 ^ N → y < 2 ^ N → refStep (mkParams K N) x y = x * y := by sorry
end IntMul.HvdH.Ref
