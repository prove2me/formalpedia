-- Prove2me | Theorems.Thm_KrohnRhodes_exists_minimal_generating
-- name    : KrohnRhodes.exists_minimal_generating
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:50.757814+00:00
-- url     : https://prove2.me/theorems/eef42d3a-d699-5deb-b48b-dae41eefc1d1
-- title:
--   Krohn Rhodes: exists minimal generating
-- statement:
--   **Every finite monoid has a minimal finite generating set.** Every finite monoid $M$ (with
--   decidable equality) has a finite generating set $A$ ($\texttt{Submonoid.closure}\,A = \top$) that
--   is $\subseteq$-minimal in the strong sense that no single generator can be dropped: for every
--   $a \in A$, $\texttt{Submonoid.closure}\,(A \setminus \{a\}) \ne \top$. (Folklore.)
--
--   *Proof sketch.* $\texttt{Finset.univ}$ generates ($1$ and all of $M$ are in the closure). Among
--   all generating finsets pick one of minimal cardinality (strong induction on `Finset.card`, or
--   well-foundedness of $<$ on $\mathbb{N}$): if some $a \in A$ could be dropped with
--   $\langle A \setminus \{a\} \rangle = \top$, the erased set would be a strictly smaller generating
--   finset, contradicting minimality.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L820-L832
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L820-L832

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

theorem KrohnRhodes.exists_minimal_generating (M : Type) [Monoid M] [Finite M] [DecidableEq M] :
    ∃ A : Finset M, Submonoid.closure (A : Set M) = ⊤ ∧
      ∀ a ∈ A, Submonoid.closure ((A.erase a : Finset M) : Set M) ≠ ⊤ := by sorry
