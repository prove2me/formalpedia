-- Prove2me | Theorems.Thm_KrohnRhodes_sgdiv_closure_monoid
-- name    : KrohnRhodes.sgdiv_closure_monoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:31.183029+00:00
-- url     : https://prove2.me/theorems/b88a3d5d-aff6-5914-a521-48d9f22e0ccb
-- title:
--   Krohn Rhodes: sgdiv closure monoid
-- statement:
--   **A faithfully represented monoid divides its constants closure.** Let $M$ be a monoid and
--   $\mathrm{act} \colon M \to^* \mathrm{End}(Q)$ an injective monoid homomorphism. Then $M$ divides
--   the constants closure `closureMonoid` as a semigroup (`SgDiv`: some subsemigroup of
--   $\overline{(Q,M)}$ maps onto $M$ by a multiplicative surjection). Used once, in the master
--   assembly `krohn_rhodes_prime_decomposition`, to pull the tower of the closure back to $M$.
--
--   *Proof sketch.* The image of $\mathrm{act}$ is contained in the closure (left disjunct of the
--   generating set, `Submonoid.subset_closure`), so $\mathrm{act}$ corestricts to a monoid
--   homomorphism $M \to^* \overline{(Q,M)}$ (`MonoidHom.codRestrict`), injective because
--   $\mathrm{act}$ is. `sgDiv_of_injective_monoidHom` turns an injective
--   monoid homomorphism into a semigroup division.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L150-L157
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L150-L157

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_FactorTower
public import Definitions.Def_KrohnRhodes_PrimeDecomposition
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green

theorem KrohnRhodes.sgdiv_closure_monoid {M Q : Type} [Monoid M] (act : M →* Function.End Q)
    (hf : Function.Injective act) : SgDiv M ↥(closureMonoid act) := by sorry
