-- Prove2me | Theorems.Thm_KrohnRhodes_dks_aux
-- name    : KrohnRhodes.dks_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:17.929067+00:00
-- url     : https://prove2.me/theorems/1830579a-bef8-4947-9264-94a59d324f24
-- title:
--   Krohn Rhodes: dks aux
-- statement:
--   **The DKS induction: closure towers with group factors dividing M.** For every $n$, every
--   finite type $Q$, every finite monoid $M$ with $\mathrm{Nat.card}\,M \le n$, and every INJECTIVE
--   monoid homomorphism $\mathrm{act} \colon M \to^* \mathrm{End}(Q)$: there is a factor list whose
--   iterated wreath product the constants closure $\overline{(Q,M)}$ (`closureMonoid`) divides
--   (`DivTowerWreath`), with every simple-group factor dividing $M$. The motive is stated over
--   closures, as in DKS, so that both recursive calls return exactly the decoration and base of the
--   main decomposition; the induction is on the monoid size only, never the state set (DKS Cor 3.2).
--
--   *Proof sketch.* Induction on the bound $n$ (the `Nat.rec` pattern of
--   `group_subquotient_faithful_aux`); the base $n = 0$ is vacuous, since a finite monoid is
--   nonempty and so has positive cardinality. DEGENERATE CASE ($Q$ subsingleton, covering
--   $Q = \emptyset$ and $|Q| = 1$): $\mathrm{End}(Q)$ is a subsingleton, hence so is the closure, and
--   the empty tower works (`divTowerWreath_nil_of_subsingleton`); the divisibility condition is
--   vacuous. GROUP CASE (every element a unit): `dks_aux_group`. NON-GROUP CASE ($Q$ nontrivial,
--   hence nonempty; some non-unit exists): choose a minimal generating finset $A$ by
--   `exists_minimal_generating` and a non-unit $c \in A$ by `exists_nonunit_generator`; set
--   $N := \langle A \setminus \{c\} \rangle$, proper by minimality, so
--   $\mathrm{Nat.card}\,N < \mathrm{Nat.card}\,M$ by `card_lt_of_proper`; also
--   $\mathrm{Nat.card}\,M_c < \mathrm{Nat.card}\,M$ by `local_divisor_card_lt`. Apply the inductive
--   hypothesis twice: at $(cQ,\ M_c,\ \mathrm{localActHom})$ — injective by `local_act_injective`
--   (here the faithfulness hypothesis is consumed), the $cQ$ Fintype instance by `Fintype.ofFinite` —
--   yielding a tower for the decoration closure with simple-group factors dividing $M_c$, hence
--   dividing $M$ through `LocalDivisor.localDivides` and `MonoidDivides.trans`; and at
--   $(Q \sqcup N,\ N,\ \mathrm{extAct})$ — injective by `ext_act_injective` — yielding a tower for
--   the base closure with simple-group factors dividing $N$, hence dividing $M$ through
--   `submonoid_divides` and `MonoidDivides.trans`. `main_decomposition` (at the containment
--   $A \setminus \{c\} \subseteq N$ by `Submonoid.subset_closure`) gives
--   $\overline{(Q,M)} \preceq \overline{(cQ, M_c)} \wr \overline{(Q \sqcup N, N)}$, and
--   `divTowerWreath_wreathStep` concatenates the two towers: factors $:=$ decoration tower $++$ base
--   tower.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L955-L1020
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L955-L1020

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

theorem KrohnRhodes.dks_aux (n : ℕ) :
    ∀ (Q : Type) [Fintype Q] (M : Type) [Monoid M] [Finite M]
      (act : M →* Function.End Q),
      Function.Injective act → Nat.card M ≤ n →
      ∃ factors : List KRFactor.{0}, DivTowerWreath ↥(closureMonoid act) factors ∧
        ∀ F ∈ factors, F.kind = KRFactorKind.simpleGroup →
          KrohnRhodes.MonoidDivides F.carrier M := by sorry
