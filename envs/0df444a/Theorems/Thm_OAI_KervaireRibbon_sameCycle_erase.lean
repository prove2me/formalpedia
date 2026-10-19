-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_sameCycle_erase
-- name    : OAI.KervaireRibbon.sameCycle_erase
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:25:30.316334+00:00
-- url     : https://prove2.me/theorems/7ee7996e-0954-406a-846e-1de03f12c287
-- title:
--   Erasing a dart preserves the other cycles
-- statement:
--   Let $\sigma$ be a permutation of $D$ and $x$ a dart that is not fixed. Let $\mathrm{erase}(\sigma,x)=(x\ \sigma x)\,\sigma$, which removes $x$ from its cycle and fixes it. For darts $d,e\ne x$,
--   $$
--   d,e\text{ lie in the same cycle of }\mathrm{erase}(\sigma,x)\iff d,e\text{ lie in the same cycle of }\sigma .
--   $$
--
--   So erasing a dart changes the cycle structure only by detaching that dart.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Suppression.lean#L37-L59

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem OAI.KervaireRibbon.sameCycle_erase (σ : Equiv.Perm D) {x d e : D} (hx : σ x ≠ x)
    (hd : d ≠ x) (he : e ≠ x) :
    (erase σ x).SameCycle d e ↔ σ.SameCycle d e := by sorry
