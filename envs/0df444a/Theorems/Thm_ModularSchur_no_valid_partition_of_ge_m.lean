-- Prove2me | Theorems.Thm_ModularSchur_no_valid_partition_of_ge_m
-- name    : ModularSchur.no_valid_partition_of_ge_m
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:39:56.19895+00:00
-- url     : https://prove2.me/theorems/eb103422-c779-4957-a11f-627607919c8b
-- title:
--   No valid $k$-partition of $[1,N]$ exists once $N \ge m$
-- statement:
--   This is the universal upper bound in its integer form.
--
--   Let $m \ge 2$ and $\ell, k \ge 1$, and suppose $N \ge m$. Then no family $P_0, \dots, P_{k-1}$ of subsets of $\mathbb{N}$ is a valid $k$-partition of $[1,N]$ into classes that are $\ell$-sum-free modulo $m$:
--
--   $$ N \ge m \implies \text{no valid } k\text{-partition of } [1,N] \text{ exists, for any } k. $$
--
--   The obstruction is the single integer $m$ itself, which lies in $[1,N]$ and reduces to $0$ modulo $m$, so whichever class receives it is not $\ell$-sum-free.
--
--   Consequently $S_m(k,\ell) \le m-1$ for every $k$ and $\ell$, uniformly in both. This is the bound that makes the search space finite and justifies capping the definition of $S_m(k,\ell)$ at $m-1$.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, Lemma 2.2 (Universal upper bound), integer form. Prior art: the paper cites this as [CMD2013, Eq. (2)]; see Chappelon, Revuelta Marchena and Sanz Dominguez, "Modular Schur numbers", Electron. J. Combin. 20(2) (2013) #P61, DOI 10.37236/2374, arXiv:1306.5635. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/IntegerBridge.lean#L164-L174

import Definitions.Def_ModularSchurIntegerBridge
import Mathlib

open ModularSchur
open Finset
variable {m : ℕ}

theorem ModularSchur.no_valid_partition_of_ge_m (hm : 2 ≤ m) {ℓ k N : ℕ}
    (hN : m ≤ N) (P : Fin k → Finset ℕ) (hP : IsValidPartitionNat m ℓ k N P) : False := by sorry
