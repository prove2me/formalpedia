-- Prove2me | Theorems.Thm_MasulloGRH_closure_image_connectedComponentOfOne_normOneIdeles_equiv
-- name    : MasulloGRH.closure_image_connectedComponentOfOne_normOneIdeles_equiv
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T20:08:23.892949+00:00
-- url     : https://prove2.me/theorems/55f124fd-7b23-4e1e-a989-59b0159fec0a
-- title:
--   The closure of the image of the identity component of the norm-one ideles in $C_F$ is $(\mathbb R/\mathbb Z)^{r_2}\times(\mathbb A_{\mathbb Q}/\mathbb Q)^{r_1+r_2-1}$
-- statement:
--   **The closure of the image of the identity component of the norm-one ideles in the idele class group is a product of circles and solenoids** (the computational half of the Artin–Tate description of the identity component of $C_F^1$).
--
--   Let $F$ be a number field, $\mathrm{GL}_1(\mathbb A_F)$ its group of ideles with the usual locally compact topology, $|g|_F=\prod_v|g_v|_v$ the idelic norm (normalized absolute values, squared at the complex places), $q\colon\mathrm{GL}_1(\mathbb A_F)\to C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$ the quotient map onto the idele class group (quotient topology), and
--   $$J_F^1=\{\,g\in\mathrm{GL}_1(\mathbb A_F) : |g|_F=1\,\}$$
--   the group of norm-one ideles with the induced topology. Let $(J_F^1)^0$ be the connected component of the identity of $J_F^1$, and $\overline{q\big((J_F^1)^0\big)}$ the closure in $C_F$ of its image, a closed subgroup of $C_F$ with the induced topology. Let $r_1$ and $r_2$ be the numbers of real and complex places of $F$, and let
--   $$\mathbf S=\mathbb A_{\mathbb Q}/\mathbb Q$$
--   be the solenoid: the quotient of the adele ring of $\mathbb Q$ by the diagonally embedded field $\mathbb Q$, a compact connected abelian group.
--
--   **Statement.** There is an isomorphism of topological groups
--   $$\overline{q\big((J_F^1)^0\big)}\ \cong\ (\mathbb R/\mathbb Z)^{r_2}\times\mathbf S^{\,r_1+r_2-1}.$$
--
--   The group $(J_F^1)^0$ consists of the ideles $g$ with $g_v=1$ at every finite place $v$, $g_w>0$ at every real place $w$, and $\prod_{w\mid\infty}|g_w|_w=1$. For $F=\mathbb Q$ both sides are trivial; for an imaginary quadratic field the closure is the image of the unit circle at the complex place, a circle. The closure is the identity component of the norm-one idele class group $C_F^1$, so the statement gives the Artin–Tate structure theorem $(C_F^1)^0\cong(\mathbb R/\mathbb Z)^{r_2}\times\mathbf S^{r_1+r_2-1}$ recalled in the proof of Proposition D.1.10.7 of the source, and with it $C_F^0\cong\mathbb R_{>0}\times(\mathbb R/\mathbb Z)^{r_2}\times\mathbf S^{r_1+r_2-1}$.
--
--   **Formalization Note.** `IdeleGroup F`, `IdeleClassGroup F`, `principalIdeles F` and `ideleNorm` are the platform definitions (units of Mathlib's `AdeleRing (𝓞 F) F`, modulo the principal ideles; the product of the normalized absolute values). $J_F^1$ enters as a subgroup `J` of `IdeleGroup F` whose elements are exactly the ideles of norm $1$ (there is exactly one such subgroup). $(J_F^1)^0$ is `Subgroup.connectedComponentOfOne J` (subspace topology of `J`), pushed to `IdeleGroup F` by `J.subtype` and to `IdeleClassGroup F` by `QuotientGroup.mk'`; the closure is `Subgroup.topologicalClosure`, with the topology induced from `IdeleClassGroup F`. The right-hand side is written additively, as `(Fin r₂ → UnitAddCircle) × (Fin (r₁ + r₂ - 1) → 𝔸_ℚ ⧸ ℚ)`, and made multiplicative by `Multiplicative`; $\mathbb A_{\mathbb Q}/\mathbb Q$ is the quotient of the additive group of `AdeleRing (𝓞 ℚ) ℚ` by the range of `algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)`, with the quotient topology. $r_1+r_2-1$ is truncated subtraction, harmless since $r_1+r_2\ge1$. The statement is `Nonempty (_ ≃ₜ* _)`: existence of a group isomorphism that is a homeomorphism.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 789, proof of Proposition D.1.10.7 (auxiliary lemma for the proof of the norm-one identity-component theorem MasulloGRH.normOneIdeleClassGroup_connectedComponentOfOne_equiv, itself recalled from [AT, Ch. IX, §1, Thm. 3]); classical reference (the section cited by the source): E. Artin, J. T. Tate, Class Field Theory, W. A. Benjamin, 1967, Ch. IX, §1

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm

open NumberField

set_option autoImplicit false

namespace MasulloGRH

theorem closure_image_connectedComponentOfOne_normOneIdeles_equiv (F : Type*) [Field F]
    [NumberField F] (J : Subgroup (IdeleGroup F))
    (hJ : ∀ g : IdeleGroup F, g ∈ J ↔ ideleNorm g = 1) :
    Nonempty ((((Subgroup.connectedComponentOfOne J).map J.subtype).map
        (QuotientGroup.mk' (principalIdeles F))).topologicalClosure ≃ₜ*
      Multiplicative ((Fin (InfinitePlace.nrComplexPlaces F) → UnitAddCircle) ×
        (Fin (InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F - 1) →
          AdeleRing (𝓞 ℚ) ℚ ⧸ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).range.toAddSubgroup))) := by sorry

end MasulloGRH
