-- Prove2me | Theorems.Thm_ModularSchur_k1_partition_iff
-- name    : ModularSchur.k1_partition_iff
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:38:36.354865+00:00
-- url     : https://prove2.me/theorems/dc066ff4-c06d-4660-acf2-df6fe412e22f
-- title:
--   With one colour, validity reduces to $\ell$-sum-freeness of the whole set
-- statement:
--   This theorem removes the partition quantifier in the single-colour case.
--
--   Let $m$ and $\ell$ be given and let $T \subseteq \mathbb{Z}/m$ be a target set. Then
--
--   $$ \big(\exists\, P_0 \text{ a valid } 1\text{-partition of } T\big) \iff T \text{ is } \ell\text{-sum-free modulo } m. $$
--
--   With a single class available there is no freedom: the one class must be $T$ itself, so asking for a valid colouring is asking whether $T$ is already safe.
--
--   This is the reduction that turns the $k = 1$ modular Schur number into a question about one explicit set rather than about the existence of a colouring, and every step of the one-colour formula is stated through it.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, the single-class reduction underlying Section 6. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/K1Theorem.lean#L25-L43

import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Mathlib

open ModularSchur
open Finset Classical

theorem ModularSchur.k1_partition_iff (m ℓ : ℕ) (T : Finset (ZMod m)) :
    (∃ P : Fin 1 → Finset (ZMod m), IsValidPartition m ℓ 1 T P) ↔
    IsEllSumFree m ℓ T := by sorry
