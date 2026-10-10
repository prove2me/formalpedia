-- Prove2me | Theorems.Thm_LandauFunction_landau_eq_sup_partition_lcm
-- name    : LandauFunction.landau_eq_sup_partition_lcm
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:33.22898+00:00
-- url     : https://prove2.me/theorems/deaaf5dd-2ee9-4b8d-b92b-a65c6ace2120
-- title:
--   Landau's function as the maximal lcm of a partition
-- statement:
--   For every natural number $n$, Landau's function equals the largest least common multiple of the parts of a partition of $n$:
--
--   $$g(n)=\max_{\lambda\vdash n}\operatorname{lcm}(\lambda_1,\dots,\lambda_k),$$
--
--   where $\lambda=(\lambda_1,\dots,\lambda_k)$ ranges over all partitions of $n$ into positive parts.
--
--   This is the bridge between the group-theoretic definition of $g$ and its arithmetic study.
--
--   **Formalization Note** Partitions are Mathlib's `Nat.Partition n`; the lcm of the empty partition of $0$ is $1$.
-- source:
--   Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), first paragraph ("Equivalently, g(n) is the largest least common multiple (lcm) of any partition of n").

import Mathlib
import Definitions.Def_LandauFunction_landau

namespace LandauFunction
theorem landau_eq_sup_partition_lcm (n : ℕ) :
    landau n = (Finset.univ : Finset (Nat.Partition n)).sup fun p => p.parts.lcm := by sorry
end LandauFunction
