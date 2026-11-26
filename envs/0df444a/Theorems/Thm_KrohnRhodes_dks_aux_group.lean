-- Prove2me | Theorems.Thm_KrohnRhodes_dks_aux_group
-- name    : KrohnRhodes.dks_aux_group
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:56.433219+00:00
-- url     : https://prove2.me/theorems/e5db8f09-96f6-4e13-b5e0-507db080dcc9
-- title:
--   Krohn Rhodes: dks aux group
-- statement:
--   **Group dispatch: the closure tower for an all-units monoid.** Let $Q$ be a finite type, $M$
--   a finite monoid all of whose elements are units, and
--   $\mathrm{act} \colon M \to^* \mathrm{End}(Q)$ a monoid homomorphism. Then there is a factor list
--   (`KRFactor` atoms at universe $0$) whose iterated wreath product the constants closure
--   $\overline{(Q,M)}$ (`closureMonoid`) divides (`DivTowerWreath`), with every simple-group factor
--   dividing $M$ (`MonoidDivides`). The aperiodic factors — here a single
--   reset atom — are unconstrained. (In DKS the group case of Corollary 3.2 is trivial; the group
--   leaves are decomposed in the proof of Theorem 4.1, by Lemma 2.9 and Corollary 2.8. Corollary 2.8
--   is replaced here by `group_subquotient_faithful_aux`, whose tower has all factors dividing the
--   group.)
--
--   *Proof sketch.* Endow $M$ with its group structure (`groupOfIsUnit`, definitionally extending the
--   given monoid). `group_decomposition` gives $\overline{(Q,M)} \preceq U(Q) \wr_M M$. The
--   decoration contributes the single aperiodic factor $\texttt{KRFactor.ofAperiodic}$ of the reset
--   submonoid — genuinely aperiodic by `reset_submonoid_aperiodic` — with its one-rung tower
--   (`divTowerWreath_ofAperiodic`). The base $M$ has the group tower
--   `group_subquotient_faithful_aux` (at $n = \mathrm{Nat.card}\,M$), whose `factorsDivide`
--   field already gives every factor (in particular every simple-group factor) dividing $M$. Assemble
--   with `divTowerWreath_wreathStep`: factors $:=$ reset atom $::$ group tower; the simple-group
--   factors all sit in the tail.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L895-L923
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L895-L923

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

theorem KrohnRhodes.dks_aux_group {Q M : Type} [Fintype Q] [Monoid M] [Finite M]
    (act : M →* Function.End Q) (_hU : ∀ m : M, IsUnit m) :
    ∃ factors : List KRFactor.{0}, DivTowerWreath ↥(closureMonoid act) factors ∧
      ∀ F ∈ factors, F.kind = KRFactorKind.simpleGroup →
        KrohnRhodes.MonoidDivides F.carrier M := by sorry
