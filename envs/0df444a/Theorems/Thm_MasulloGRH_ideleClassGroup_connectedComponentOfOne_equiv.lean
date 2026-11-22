-- Prove2me | Theorems.Thm_MasulloGRH_ideleClassGroup_connectedComponentOfOne_equiv
-- name    : MasulloGRH.ideleClassGroup_connectedComponentOfOne_equiv
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T17:01:03.828239+00:00
-- url     : https://prove2.me/theorems/b36f20e0-acec-4119-a943-7fc47c26c40d
-- title:
--   Artin–Tate: the identity component of the idele class group is $C_F^0\cong\mathbb R_{>0}\times(\mathbb R/\mathbb Z)^{r_2}\times(\mathbb A_{\mathbb Q}/\mathbb Q)^{r_1+r_2-1}$
-- statement:
--   **Structure of the connected component of the idele class group** (Artin–Tate; recalled in the proofs of Propositions D.1.10.7 and D.1.10.9 of the source).
--
--   Let $F$ be a number field with $r_1$ real places and $r_2$ complex places, $\mathbb A_F$ its ring of adeles, $\mathrm{GL}_1(\mathbb A_F)$ the group of ideles with its usual locally compact topology, and
--   $$C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$$
--   the idele class group with the quotient topology. Let $C_F^0$ be the connected component of the identity of $C_F$, a closed subgroup, with the induced topology. Let
--   $$\mathbf S=\mathbb A_{\mathbb Q}/\mathbb Q$$
--   be the quotient of the adele ring of $\mathbb Q$ by the diagonally embedded field $\mathbb Q$, a compact connected abelian group (the *solenoid*; the source also writes it as $\varprojlim_{x\mapsto Nx}\mathbb R/\mathbb Z$).
--
--   **Statement.** There is an isomorphism of topological groups
--   $$C_F^0\ \cong\ \mathbb R_{>0}\times(\mathbb R/\mathbb Z)^{r_2}\times\mathbf S^{\,r_1+r_2-1}.$$
--
--   For $F=\mathbb Q$ this says $C_{\mathbb Q}^0\cong\mathbb R_{>0}$, and for an imaginary quadratic field $C_F^0\cong\mathbb R_{>0}\times\mathbb R/\mathbb Z\cong\mathbb C^\times$. The number $r_1+r_2-1$ of solenoids is the rank of the unit group of $F$. The source uses the theorem to describe the compact group $(C_F^1)^0\cong(\mathbb R/\mathbb Z)^{r_2}\times\mathbf S^{r_1+r_2-1}$, to compute the Lie algebra of one-parameter subgroups $\mathcal L(C_F)=\mathcal L(C_F^0)$, of dimension $1+(r_1+2r_2-1)=[F:\mathbb Q]$, and to produce the one-parameter subgroups $\gamma_j$ entering its families of seminorms on $\mathcal S(C_F)$.
--
--   **Formalization Note.** `IdeleClassGroup F` is the platform definition (units of Mathlib's `AdeleRing (𝓞 F) F` with the units topology, modulo the principal ideles, with the quotient topology), and $C_F^0$ is `Subgroup.connectedComponentOfOne (IdeleClassGroup F)`. The right-hand side is written additively, as `ℝ × (Fin r₂ → UnitAddCircle) × (Fin (r₁ + r₂ - 1) → 𝔸_ℚ ⧸ ℚ)` with $\mathbb R_{>0}\cong\mathbb R$ by the logarithm, and turned into a multiplicative group by `Multiplicative`; $\mathbb A_{\mathbb Q}/\mathbb Q$ is the quotient of the additive group of `AdeleRing (𝓞 ℚ) ℚ` by the range of `algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)`, with the quotient topology. $r_1$ and $r_2$ are `InfinitePlace.nrRealPlaces F` and `InfinitePlace.nrComplexPlaces F`; the subtraction $r_1+r_2-1$ is the truncated subtraction of natural numbers, which is the true one since $r_1+r_2\ge1$. The statement is `Nonempty (_ ≃ₜ* _)`: existence of a group isomorphism that is a homeomorphism.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 791 (proof of Proposition D.1.10.9) and p. 789 (proof of Proposition D.1.10.7); classical reference (as cited in the source): E. Artin, J. T. Tate, Class Field Theory, W. A. Benjamin, 1967, Ch. IX, §1, Thm. 3

import Mathlib
import Definitions.Def_MasulloGRH_HeckeLFunction

open NumberField

set_option autoImplicit false

namespace MasulloGRH

theorem ideleClassGroup_connectedComponentOfOne_equiv (F : Type*) [Field F] [NumberField F] :
    Nonempty (Subgroup.connectedComponentOfOne (IdeleClassGroup F) ≃ₜ*
      Multiplicative (ℝ × (Fin (InfinitePlace.nrComplexPlaces F) → UnitAddCircle) ×
        (Fin (InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F - 1) →
          AdeleRing (𝓞 ℚ) ℚ ⧸ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).range.toAddSubgroup))) := by
  sorry

end MasulloGRH
