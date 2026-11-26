-- Prove2me | Theorems.Thm_KrohnRhodes_card_lt_of_proper
-- name    : KrohnRhodes.card_lt_of_proper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:43.695859+00:00
-- url     : https://prove2.me/theorems/f3e6b949-70ef-4cb3-a1d6-1ab0a369093b
-- title:
--   Krohn Rhodes: card lt of proper
-- statement:
--   **A proper submonoid of a finite monoid is strictly smaller.** For a finite monoid $M$ and a
--   submonoid $N \ne \top$, $\mathrm{Nat.card}\,N < \mathrm{Nat.card}\,M$. Applied by `dks_aux` to
--   $N = \langle A \setminus \{c\} \rangle$, proper by the minimality clause of
--   `exists_minimal_generating`, to make the second recursive call decrease.
--
--   *Proof sketch.* $N \ne \top$ makes the carrier set of $N$ a *proper* subset of the universe set
--   of $M$ (`Set.ssubset_univ_iff`; carrier-set equality converts back to $N = \top$ via
--   `SetLike.coe_set_eq` and `Submonoid.coe_top`). A proper subset of a finite set has strictly
--   smaller cardinality (`Set.Finite.card_lt_card` at `Set.finite_univ`), and `Nat.card_univ`
--   identifies $\mathrm{Nat.card}\,(\mathrm{Set.univ})$ with $\mathrm{Nat.card}\,M$.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L867-L873
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L867-L873

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

theorem KrohnRhodes.card_lt_of_proper {M : Type} [Monoid M] [Finite M] {N : Submonoid M}
    (hN : N ≠ ⊤) : Nat.card ↥N < Nat.card M := by sorry
