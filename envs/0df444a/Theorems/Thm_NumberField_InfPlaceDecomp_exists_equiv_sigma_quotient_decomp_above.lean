-- Prove2me | Theorems.Thm_NumberField_InfPlaceDecomp_exists_equiv_sigma_quotient_decomp_above
-- name    : NumberField.InfPlaceDecomp.exists_equiv_sigma_quotient_decomp_above
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/abf2887e-9212-5818-847c-a93f89f638e2
-- title:
--   Infinite places of a Galois extension as a G-set
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra such that $K/E$ is Galois, and write $G = K \simeq_{\mathrm{alg}[E]} K$ for its Galois group, acting on infinite places in the usual way. For each infinite place $v$ of $E$, let $\mathrm{above}\,E\,K\,v$ denote the place of $K$ over $v$ chosen by [`NumberField.ArchIdele.above`](def/NumberField_ArchimedeanIdeleModule.html#L155) (a choice extracted from the existence statement `exists_above`), and let [`NumberField.InfPlaceDecomp.decomp`](def/NumberField_ArchimedeanIdeleModule.html#L23) of that place be its decomposition group, namely the stabiliser `MulAction.stabilizer` of the place in $G$. The theorem asserts the existence of a bijection
--   $$e : \mathrm{InfinitePlace}\,K \;\simeq\; \coprod_{v \in \mathrm{InfinitePlace}\,E} G / \mathrm{decomp}\bigl(\mathrm{above}\,E\,K\,v\bigr),$$
--   where the coproduct is the dependent sigma type over the infinite places of $E$ and each summand is the quotient of $G$ by the stabiliser subgroup, such that $e$ is $G$-equivariant: for every $\sigma \in G$ and every infinite place $w$ of $K$, $e(\sigma \cdot w) = \sigma \cdot e(w)$, the action on the sigma type being left translation of cosets within each fibre, leaving the index $v$ fixed. Only the existence of such an equivariant bijection is asserted; no particular $e$ is named in the conclusion.
--
--   This is the orbit–stabiliser description of the archimedean places of a Galois extension of number fields as a $G$-set: a disjoint union, over the infinite places of the base, of the coset spaces of the decomposition groups. It is used in the computation of ranks of invariants of $S$-unit groups modulo $p$, where it transports statements indexed by places of $K$ to statements indexed by cosets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfPlaceDecomp_exists_equiv_sigma_quotient_decomp_above.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module IsDedekindDomain NumberField NumberField.LevelArith
open scoped Classical NumberField.LevelArith

theorem NumberField.InfPlaceDecomp.exists_equiv_sigma_quotient_decomp_above
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K] :
    ∃ e : NumberField.InfinitePlace K ≃
        Σ v : NumberField.InfinitePlace E, (K ≃ₐ[E] K) ⧸ NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v),
      ∀ (σ : K ≃ₐ[E] K) (w : NumberField.InfinitePlace K), e (σ • w) = σ • e w := by sorry
