-- Prove2me | Theorems.Thm_KrohnRhodes_ext_act_injective
-- name    : KrohnRhodes.ext_act_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:06.011258+00:00
-- url     : https://prove2.me/theorems/0b9bf3c7-88a6-5c35-a4f9-a8b3b56c4a5a
-- title:
--   Krohn Rhodes: ext act injective
-- statement:
--   **The extension action is faithful.** For every monoid homomorphism
--   $\mathrm{act} \colon M \to^* \mathrm{End}(Q)$ and submonoid $N \le M$, the extension action
--   `extAct` is injective — with NO faithfulness hypothesis on $\mathrm{act}$: the $\mathrm{inr}$
--   component alone separates elements (evaluate at $\mathrm{inr}\,1$). Supplies the injectivity
--   hypothesis when the induction `dks_aux` recurses into $(Q \sqcup N, N)$.
--
--   *Proof sketch.* If $n_1, n_2 \in N$ induce the same transformation of $Q \sqcup N$, evaluate at
--   $\mathrm{inr}\,1$: $\mathrm{inr}\,(n_1 \cdot 1) = \mathrm{inr}\,(n_2 \cdot 1)$, so $n_1 = n_2$ by
--   injectivity of $\mathrm{inr}$ and `mul_one`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L525-L531
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L525-L531

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

theorem KrohnRhodes.ext_act_injective {M Q : Type} [Monoid M] (act : M →* Function.End Q)
    (N : Submonoid M) : Function.Injective (extAct act N) := by sorry
