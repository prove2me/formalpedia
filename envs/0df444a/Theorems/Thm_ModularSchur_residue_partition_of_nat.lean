-- Prove2me | Theorems.Thm_ModularSchur_residue_partition_of_nat
-- name    : ModularSchur.residue_partition_of_nat
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:47:31.160132+00:00
-- url     : https://prove2.me/theorems/7f864ba3-1bd7-4ab4-8775-b8ae2e9fb6cf
-- title:
--   A valid integer partition of $[1,N]$ induces a valid residue partition
-- statement:
--   This is the forward half of the residue reduction.
--
--   Let $m \ge 2$ and $\ell, k, N$ be given with $N \le m-1$. If $P_0, \dots, P_{k-1} \subseteq \mathbb{N}$ is a valid $k$-partition of $[1,N]$ into classes that are $\ell$-sum-free modulo $m$, then there is a family $Q_0, \dots, Q_{k-1} \subseteq \mathbb{Z}/m$ with
--
--   $$ Q_0, \dots, Q_{k-1} \text{ a valid } k\text{-partition of } \mathrm{stableResidues}(m,N) = \{\overline{1}, \dots, \overline{N}\}. $$
--
--   The hypothesis $N \le m-1$ is what makes this work: on $[1,N]$ the reduction map $\mathbb{N} \to \mathbb{Z}/m$ is injective and misses $0$, so the classes transport without collapsing into one another.
--
--   Together with its converse this is what licenses the whole development to argue about residues while stating its conclusions about integers.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, Lemma 2.1 (Residue reduction), forward direction. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/IntegerBridge.lean#L74-L123

import Definitions.Def_ModularSchurIntegerBridge
import Definitions.Def_ModularSchurPartition
import Mathlib

open ModularSchur
open Finset
variable {m : ℕ}

theorem ModularSchur.residue_partition_of_nat (hm : 2 ≤ m) {ℓ k N : ℕ} (hN : N ≤ m - 1)
    {P : Fin k → Finset ℕ} (hP : IsValidPartitionNat m ℓ k N P) :
    ∃ Q : Fin k → Finset (ZMod m),
      IsValidPartition m ℓ k (stableResidues m N) Q := by sorry
