-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_exists_cycle_coordinates
-- name    : OAI.KervaireRibbon.exists_cycle_coordinates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:24:43.831607+00:00
-- url     : https://prove2.me/theorems/7590e84c-cd1c-467a-ad9c-1653d2473e17
-- title:
--   Cycle coordinates of a permutation
-- statement:
--   Let $\sigma$ be a permutation of a finite set $D$. There are lengths $n_z+1$, one for each cycle $z$ of $\sigma$, and a bijection
--   $$
--   e:\ \textstyle\bigsqcup_z\{0,\dots,n_z\}\to D
--   $$
--   such that $\sigma(e(z,i))=e(z,i+1\bmod n_z+1)$ for all $z$ and $i$.
--
--   In these coordinates every cycle of $\sigma$ is a cyclic rotation, fixed points included as cycles of length one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PermutationCycles.lean#L78-L97

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem OAI.KervaireRibbon.exists_cycle_coordinates (σ : Equiv.Perm D) :
    ∃ (n : Cycles σ → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D),
      ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩ := by sorry
