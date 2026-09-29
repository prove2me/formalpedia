-- Prove2me | Theorems.Thm_ModularSchur_nat_partition_of_residue
-- name    : ModularSchur.nat_partition_of_residue
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:39:19.699545+00:00
-- url     : https://prove2.me/theorems/4c8cc266-44bb-4914-aeb6-89ceb23880a5
-- title:
--   A valid residue partition induces a valid integer partition of $[1,N]$
-- statement:
--   This is the backward half of the residue reduction.
--
--   Let $m \ge 2$ and $\ell, k, N$ be given with $N \le m-1$. If $Q_0, \dots, Q_{k-1} \subseteq \mathbb{Z}/m$ is a valid $k$-partition of $\mathrm{stableResidues}(m,N) = \{\overline{1}, \dots, \overline{N}\}$ into $\ell$-sum-free classes, then there is a family $P_0, \dots, P_{k-1} \subseteq \mathbb{N}$ with
--
--   $$ P_0, \dots, P_{k-1} \text{ a valid } k\text{-partition of } [1,N] \text{ into classes }\ell\text{-sum-free modulo } m. $$
--
--   Each integer class is recovered as the preimage of its residue class inside $[1,N]$.
--
--   This direction is what turns a residue-level construction into an admissible colouring of an actual integer interval, and so it is the half that carries every lower bound back to the integer-level $S_m(k,\ell)$.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, Lemma 2.1 (Residue reduction), backward direction. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/IntegerBridge.lean#L125-L150

import Definitions.Def_ModularSchurIntegerBridge
import Definitions.Def_ModularSchurPartition
import Mathlib

open ModularSchur
open Finset
variable {m : ℕ}

theorem ModularSchur.nat_partition_of_residue (_hm : 2 ≤ m) {ℓ k N : ℕ} (_hN : N ≤ m - 1)
    {Q : Fin k → Finset (ZMod m)} (hQ : IsValidPartition m ℓ k (stableResidues m N) Q) :
    ∃ P : Fin k → Finset ℕ, IsValidPartitionNat m ℓ k N P := by sorry
