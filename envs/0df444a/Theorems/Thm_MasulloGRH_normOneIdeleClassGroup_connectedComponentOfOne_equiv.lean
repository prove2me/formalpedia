-- Prove2me | Theorems.Thm_MasulloGRH_normOneIdeleClassGroup_connectedComponentOfOne_equiv
-- name    : MasulloGRH.normOneIdeleClassGroup_connectedComponentOfOne_equiv
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T19:15:56.727802+00:00
-- url     : https://prove2.me/theorems/dcb7dbc6-4f21-4a00-a44a-414ed400bde3
-- title:
--   Artin–Tate, norm-one form: the identity component of $C_F^1$ is $(\mathbb R/\mathbb Z)^{r_2}\times(\mathbb A_{\mathbb Q}/\mathbb Q)^{r_1+r_2-1}$
-- statement:
--   **Structure of the identity component of the norm-one idele class group** (Artin–Tate; recalled in the proof of Proposition D.1.10.7 of the source).
--
--   Let $F$ be a number field with $r_1$ real places and $r_2$ complex places, $\mathrm{GL}_1(\mathbb A_F)$ its group of ideles with the usual locally compact topology, $|g|_F=\prod_v|g_v|_v$ the idelic norm (normalized absolute values, squared at the complex places), and
--   $$C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$$
--   the idele class group with the quotient topology. By the product formula the norm is trivial on $F^\times$, and the classes of the ideles of norm $1$ form a closed subgroup
--   $$C_F^1=\{\,gF^\times : |g|_F=1\,\}\subset C_F,$$
--   the norm-one idele class group, with the induced topology; it is compact. Let $(C_F^1)^0$ be the connected component of the identity of $C_F^1$, with the induced topology, and let
--   $$\mathbf S=\mathbb A_{\mathbb Q}/\mathbb Q$$
--   be the solenoid: the quotient of the adele ring of $\mathbb Q$ by the diagonally embedded field $\mathbb Q$, a compact connected abelian group.
--
--   **Statement.** There is an isomorphism of topological groups
--   $$(C_F^1)^0\ \cong\ (\mathbb R/\mathbb Z)^{r_2}\times\mathbf S^{\,r_1+r_2-1}.$$
--
--   For $F=\mathbb Q$ the group $(C_{\mathbb Q}^1)^0$ is trivial ($C_{\mathbb Q}^1\cong\widehat{\mathbb Z}^\times$ is profinite), and for an imaginary quadratic field it is a circle. The group $(C_F^1)^0$ is the maximal compact subgroup of the identity component $C_F^0\cong\mathbb R_{>0}\times(C_F^1)^0$ of $C_F$. The source uses the statement in the proof of Proposition D.1.10.7 to describe the compact part of $C_F^0$ and its Lie algebra of one-parameter subgroups; together with the splitting $C_F\cong\mathbb R_{>0}\times C_F^1$ given by a continuous section of the norm it yields the structure theorem $C_F^0\cong\mathbb R_{>0}\times(\mathbb R/\mathbb Z)^{r_2}\times\mathbf S^{r_1+r_2-1}$ used in the proof of Proposition D.1.10.9.
--
--   **Formalization Note.** `IdeleClassGroup F` and `ideleNorm` are the platform definitions (units of Mathlib's `AdeleRing (𝓞 F) F` modulo the principal ideles; the product of the normalized absolute values over all places). The subgroup $C_F^1$ enters as a subgroup `K` of `IdeleClassGroup F` whose elements are exactly the classes of the ideles of norm $1$ (there is exactly one such subgroup), and $(C_F^1)^0$ is `Subgroup.connectedComponentOfOne K`, computed in the subspace topology of `K`. The right-hand side is written additively, as `(Fin r₂ → UnitAddCircle) × (Fin (r₁ + r₂ - 1) → 𝔸_ℚ ⧸ ℚ)`, and made multiplicative by `Multiplicative`; $\mathbb A_{\mathbb Q}/\mathbb Q$ is the quotient of the additive group of `AdeleRing (𝓞 ℚ) ℚ` by the range of `algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)`, with the quotient topology. $r_1+r_2-1$ is truncated subtraction of natural numbers, harmless since $r_1+r_2\ge1$. The statement is `Nonempty (_ ≃ₜ* _)`: existence of a group isomorphism that is a homeomorphism.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 789, proof of Proposition D.1.10.7 (auxiliary lemma for the proof of the identity-component theorem MasulloGRH.ideleClassGroup_connectedComponentOfOne_equiv, pp. 789, 791); classical reference (as cited in the source): E. Artin, J. T. Tate, Class Field Theory, W. A. Benjamin, 1967, Ch. IX, §1, Thm. 3

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm

open NumberField

set_option autoImplicit false

namespace MasulloGRH

theorem normOneIdeleClassGroup_connectedComponentOfOne_equiv (F : Type*) [Field F]
    [NumberField F] (K : Subgroup (IdeleClassGroup F))
    (hK : ∀ x : IdeleClassGroup F,
      x ∈ K ↔ ∃ g : IdeleGroup F, (QuotientGroup.mk g : IdeleClassGroup F) = x ∧ ideleNorm g = 1) :
    Nonempty (Subgroup.connectedComponentOfOne K ≃ₜ*
      Multiplicative ((Fin (InfinitePlace.nrComplexPlaces F) → UnitAddCircle) ×
        (Fin (InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F - 1) →
          AdeleRing (𝓞 ℚ) ℚ ⧸ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).range.toAddSubgroup))) := by sorry

end MasulloGRH
