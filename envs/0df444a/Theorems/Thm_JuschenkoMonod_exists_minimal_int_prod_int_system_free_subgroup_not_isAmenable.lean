-- Prove2me | Theorems.Thm_JuschenkoMonod_exists_minimal_int_prod_int_system_free_subgroup_not_isAmenable
-- name    : JuschenkoMonod.exists_minimal_int_prod_int_system_free_subgroup_not_isAmenable
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:32:24.899063+00:00
-- url     : https://prove2.me/theorems/22b03d68-63ad-4eb8-91d0-c98311c0e38d
-- title:
--   Elek–Monod — the topological full group of a minimal Cantor ℤ²-system can contain a free subgroup of rank 2, and fail to be amenable
-- statement:
--   There is a Cantor space $C$ with an action of $\mathbf Z^2$ by homeomorphisms that is minimal (every closed $\mathbf Z^2$-invariant set is $\emptyset$ or $C$), whose topological full group contains a free subgroup of rank $2$ and is not amenable.
--
--   *Formalization note.* "Two commuting homeomorphisms" is an action of $\mathbf Z^2$ by homeomorphisms. "This statement fails" (Theorem A) is stated as non-amenability of the topological full group, and "can contain non-abelian free subgroups" as the existence of an injective homomorphism from the free group on two generators.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 776, the Elek–Monod ℤ²-system, which cites Elek, G. and Monod, N., On the topological full group of a minimal Cantor ℤ²-system, Proc. Amer. Math. Soc. 141 (2013) 3549–3552, https://doi.org/10.1090/S0002-9939-2013-11654-0

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_CantorSystems
import Definitions.Def_Chou_Classes
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem exists_minimal_int_prod_int_system_free_subgroup_not_isAmenable :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : AddAction (ℤ × ℤ) C),
      CantorSystems.IsCantorSpace C ∧ (∀ γ : ℤ × ℤ, Continuous fun x : C => γ +ᵥ x) ∧
      IsMinimalAction (ℤ × ℤ) C ∧
      ¬ Chou.NoFreeSubgroupOfRankTwo (CantorSystems.topologicalFullGroup (ℤ × ℤ) C) ∧
      ¬ Garrido.IsAmenable (CantorSystems.topologicalFullGroup (ℤ × ℤ) C) := by
  sorry

end JuschenkoMonod
