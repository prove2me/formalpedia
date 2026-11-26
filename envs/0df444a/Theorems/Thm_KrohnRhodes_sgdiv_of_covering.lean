-- Prove2me | Theorems.Thm_KrohnRhodes_sgdiv_of_covering
-- name    : KrohnRhodes.sgdiv_of_covering
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:33.326423+00:00
-- url     : https://prove2.me/theorems/f036eda9-cfa0-4f75-aa23-f04a8f3134e7
-- title:
--   Krohn Rhodes: sgdiv of covering
-- statement:
--   **Division from covering: covered generators yield a wreath divisor.** In the setting of
--   `Covers`, let $\varphi \colon P \times X \to R$ be surjective, let $T$ be a submonoid of
--   $\mathrm{End}(R)$, and let $S \subseteq \mathrm{End}(R)$ generate $T$
--   ($\texttt{Submonoid.closure}\,S = T$). If every $t \in S$ is covered by some $w \in A \wr_X B$,
--   then $T$ divides $A \wr_X B$ as a semigroup (`SgDiv`). This is the division-from-covering
--   argument of DKS §2.3.
--
--   *Proof sketch.* First, every $t \in T = \langle S \rangle$ is covered by some wreath element: by
--   induction over the closure representation (`Submonoid.closure_induction`), generators are covered
--   by hypothesis, $1$ is covered by `covers_one`, and products of covered elements are covered by
--   `covers_mul`. Let $V := \{w \mid \exists t \in T,\ w \text{ covers } t\}$: it is closed under
--   products by `covers_mul` (the covered transformations multiply inside the submonoid $T$), so $V$
--   is a subsemigroup of the wreath. Define $\psi \colon V \to T$ sending $w$ to THE transformation
--   it covers: well-defined by `covers_unique` (with surjectivity of $\varphi$) plus choice, and
--   multiplicative by `covers_mul` together with `covers_unique` (both sides of the multiplicativity
--   equation cover the same product element). $\psi$ is surjective onto $T$: a $t \in T$ is covered
--   by some $w$ by the first step, $w \in V$, and the decoded transformation of $w$ is $t$ by
--   `covers_unique`.
--
--   Source: https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L274-L315
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean#L274-L315

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

theorem KrohnRhodes.sgdiv_of_covering {A B P X R : Type} [Monoid A] [Monoid B] [MulAction A P]
    [MulAction B X] {φ : P × X → R} (_hφ : Function.Surjective φ)
    (S : Set (Function.End R)) (T : Submonoid (Function.End R))
    (_hgen : Submonoid.closure S = T)
    (_hcov : ∀ t ∈ S, ∃ w : WreathProduct A B X, Covers φ w t) :
    SgDiv ↥T (WreathProduct A B X) := by sorry
