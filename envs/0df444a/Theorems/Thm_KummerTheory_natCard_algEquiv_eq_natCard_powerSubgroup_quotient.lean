-- Prove2me | Theorems.Thm_KummerTheory_natCard_algEquiv_eq_natCard_powerSubgroup_quotient
-- name    : KummerTheory.natCard_algEquiv_eq_natCard_powerSubgroup_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/d3ad1dd9-e956-5b16-89ec-060aa3410a9f
-- title:
--   Kummer theory: #Gal(L/K) as a power-subgroup index
-- statement:
--   Let $K$ and $L$ be fields in `Type`, with $L$ a $K$-algebra that is finite-dimensional over $K$ and Galois over $K$, and let $n$ be a natural number. Assume: the set `primitiveRoots n K` of primitive $n$-th roots of unity in $K$ is nonempty; any two elements $\sigma,\tau$ of the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$ commute; and $\sigma^n = 1$ for every such $\sigma$. Write $P =$ [`groupCohomology.Kummer.powerSubgroup K L n`](def/GroupCohomology_Kummer.html#L157) for the subgroup of $K^\times$ consisting of those units $a$ for which $\mathrm{algebraMap}_{K,L}(a) = \alpha^n$ for some $\alpha \in L^\times$, i.e. $K^\times \cap (L^\times)^n$. Then the cardinality of $L \simeq_{\mathrm{alg}[K]} L$ equals the cardinality of the quotient of $P$ by the subgroup of $P$ induced by the range of the $n$-th power homomorphism `powMonoidHom n` on $K^\times$, that is, $\#\mathrm{Gal}(L/K) = [\,K^\times \cap (L^\times)^n : (K^\times)^n\,]$. Both sides are natural-number cardinalities in the sense of `Nat.card`.
--
--   This is the numerical form of Kummer theory for a finite abelian extension of exponent dividing $n$ over a field containing a primitive $n$-th root of unity. It feeds into the identification of the power subgroup as a closure joined with the range of the power map for splitting fields, and into the idelic statement used for the norm of unit ideles in a Galois extension of a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_KummerTheory_natCard_algEquiv_eq_natCard_powerSubgroup_quotient.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem KummerTheory.natCard_algEquiv_eq_natCard_powerSubgroup_quotient (K L : Type) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] {n : ℕ} (hμ : (primitiveRoots n K).Nonempty)
    (hcomm : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1) :
    Nat.card (L ≃ₐ[K] L)
      = Nat.card (groupCohomology.Kummer.powerSubgroup K L n ⧸
          ((powMonoidHom n : Kˣ →* Kˣ).range).subgroupOf (groupCohomology.Kummer.powerSubgroup K L n)) := by sorry
