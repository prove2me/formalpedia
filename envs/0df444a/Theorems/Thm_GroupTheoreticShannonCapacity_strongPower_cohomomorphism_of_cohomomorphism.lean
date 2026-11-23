-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_strongPower_cohomomorphism_of_cohomomorphism
-- name    : GroupTheoreticShannonCapacity.strongPower_cohomomorphism_of_cohomomorphism
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:26:56.826857+00:00
-- url     : https://prove2.me/theorems/43064f6e-808d-4f85-8aa5-63e97a4d344c
-- title:
--   Group Theoretic Shannon Capacity: strong Power cohomomorphism of cohomomorphism
-- statement:
--   A cohomomorphism from G to H extends to a cohomomorphism from G^⊠n to H^⊠n.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L512-L545
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L512-L545

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
set_option autoImplicit true
open GroupTheoreticShannonCapacity

theorem GroupTheoreticShannonCapacity.strongPower_cohomomorphism_of_cohomomorphism (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W) (hf : ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v))
    (n : ℕ) :
    let fn := fun x : Fin n → V => fun i => f (x i)
    ∀ x y, x ≠ y → ¬(strongPower G n).Adj x y →
      fn x ≠ fn y ∧ ¬(strongPower H n).Adj (fn x) (fn y) := by sorry
