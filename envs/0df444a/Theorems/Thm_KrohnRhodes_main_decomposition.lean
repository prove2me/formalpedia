-- Prove2me | Theorems.Thm_KrohnRhodes_main_decomposition
-- name    : KrohnRhodes.main_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:35.989434+00:00
-- url     : https://prove2.me/theorems/417e1688-3e13-5f5c-81a5-ea930e760642
-- title:
--   Krohn Rhodes: main decomposition
-- statement:
--   **Main decomposition: the closure divides local-divisor wreath extension.** Let $M$ be a
--   monoid with decidable equality, $Q$ a nonempty type,
--   $\mathrm{act} \colon M \to^* \mathrm{End}(Q)$, $A$ a finite generating set of $M$
--   ($\texttt{Submonoid.closure}\,A = \top$), $c \in M$, and $N \le M$ a submonoid containing
--   $A \setminus \{c\}$. Then the constants closure $\overline{(Q, M)}$ (`closureMonoid`) divides, as
--   a semigroup, the wreath product
--   $\overline{(cQ, M_c)} \wr_{Q \sqcup N} \overline{(Q \sqcup N, N)}$ of `cover_const_end`. This is a
--   monoid-level form of DKS Theorem 3.1 (semigroup division; any submonoid
--   $N \supseteq A \setminus \{c\}$); $c \in A$ is not needed (if $c \notin A$, family 3 is simply
--   unused). No injectivity of $\mathrm{act}$ is needed here.
--
--   *Proof sketch.* Apply `sgdiv_of_covering` with the decoding $\varphi$ of `dksProj` — surjective
--   by `dks_proj_surjective` ($Q$ nonempty) — and the generating set
--   $\mathrm{act}(A) \cup \{\overline{x}\}$ of the closure, which generates by `closure_monoid_gen`
--   at the hypothesis $\langle A \rangle = \top$. Coverage of the generators: constants
--   $\overline{x}$ by `cover_const_end`; $\mathrm{act}(a)$ for $a \in A$, $a \ne c$ by
--   `cover_act_of_mem` applied at the member of $N$ that the containment hypothesis produces from
--   $a$; and $\mathrm{act}(c)$ by `cover_act_c`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L686-L708
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L686-L708

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

theorem KrohnRhodes.main_decomposition {M Q : Type} [Monoid M] [DecidableEq M] [Nonempty Q]
    (act : M →* Function.End Q) (A : Finset M)
    (_hA : Submonoid.closure (A : Set M) = ⊤) (c : M) (N : Submonoid M)
    (_hN : ((A.erase c : Finset M) : Set M) ⊆ (N : Set M)) :
    SgDiv ↥(closureMonoid act)
      (WreathProduct ↥(closureMonoid (localActHom act c))
        ↥(closureMonoid (extAct act N)) (Q ⊕ ↥N)) := by sorry
