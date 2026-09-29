-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_reductionModL_eq_zero_of_spPic0_eq_zero_and_isPlaceReductionModL_sp
-- name    : ModularCurve.PlaceSpecialization.reductionModL_eq_zero_of_spPic0_eq_zero_and_isPlaceReductionModL_sp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/f09397ec-0d62-5a2d-bb4e-c35a6b4f22b9
-- title:
--   Place specialisation refines reduction mod ℓ on J₀(N)
-- statement:
--   Let $N\ge 1$ and let $\ell$ be a prime with $\ell\nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $\ell$, i.e. $\ell$ is a nonunit of $A$; assume the residue field of $A$ is algebraically closed of characteristic $\ell$. Let `data` consist of a monic $\Phi\in\mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ vanishing on the pair $(j(q),j(q^{\ell}))$, satisfying the Kronecker congruence $\Phi \equiv (C(X)^{\ell}-X)(C(X)-X^{\ell}) \pmod \ell$ after bivariate reduction, and assume that the two base-changed degeneracy inclusions `heckeAlphaBar` and `heckeBetaBar` from the level-$N$ to the level-$N\ell$ modular function field over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Let $S$ be a `PlaceSpecialization` for these data relative to $A$, the residue map of $A$ and the identity parameters above: it packages a map `sp` sending places of $\overline{\mathbb{Q}}$-function field `modularFunctionFieldBar N` to places of `modularFunctionFieldC` over the residue field, a group homomorphism `spPic0` on degree-zero divisor classes, together with the compatibility clauses for orders of $j$-type coordinates. Then firstly every $x$ in `JZero N` with $S.\mathrm{spPic0}\,x=0$ satisfies $\mathrm{reductionModL}\,A\,N\,x=0$; and secondly, provided `JZero N` has a nonzero element, the map `sp`, transported along the identification `modularFunctionFieldC = modularFunctionFieldFullC` valid since $\ell\nmid N$, satisfies `IsPlaceReductionModL A N`, i.e. it is a reduction of places along $A$ and its residue map.
--
--   This is the comparison, in the style of Deuring's reduction of function fields at a prime of the constant field, between a place specialisation of $X_0(N)$ at a place above $\ell\nmid N$ and the mod-$\ell$ reduction map on $J_0(N)$: the kernel of the specialisation on degree-zero classes is contained in the kernel of the reduction, and in positive genus the induced map on places is itself a reduction of places. It is used in the passage from specialisation data to the vanishing of prime-to-$\ell$ torsion classes and in the existence statements for place specialisations with prescribed prolongation and width data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_reductionModL_eq_zero_of_spPic0_eq_zero_and_isPlaceReductionModL_sp.lean

import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ReductionModL
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ValuationSubring AlgebraicCurve IsLocalRing
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem ModularCurve.PlaceSpecialization.reductionModL_eq_zero_of_spPic0_eq_zero_and_isPlaceReductionModL_sp
    (N : ℕ) [NeZero N]
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (S : PlaceSpecialization A ℓ N data hKr (ResidueField ↥A)
        (IsLocalRing.residue ↥A) hα hβ) :
    (∀ x : JZero N, S.spPic0 x = 0 → reductionModL A N x = 0) ∧
    ((∃ x : JZero N, x ≠ 0) →
      IsPlaceReductionModL A N (fun P =>
        (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) ℓ N
          hℓN).symm ▸ S.sp P)) := by sorry
