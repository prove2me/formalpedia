-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/748b218d-604a-58a8-a4d3-6b288c28ec44
-- title:
--   Reduction relation at j-integral functions pins down spPlace P
-- statement:
--   Fix $N \ge 1$ and a prime $\ell$, and let $A$ be a valuation subring of an algebraic closure of $\mathbb{Q}$ whose residue field $k =$ `IsLocalRing.ResidueField A` has characteristic $\ell$. Let `fm` be a fibre model of level $N$ over $A$ in characteristic $\ell$ with reduction map the residue map $A \to k$, let `dataAll` assign to each nonzero divisor $d$ of $N$ a modular polynomial datum (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(d)$ vanishing at the $q$-expansion $j_{q,d}$ under `evalAtJ`), and assume the image of $\Phi$ for $d = N$ in $k[X][Y]$, viewed over $k(X)$, is separable. Let $R$ be a regular prolongation of $A$ to `modularFunctionFieldBar N` with residues in `modularFunctionFieldC k N`: a valuation subring `R.integers` meeting the constants exactly in $A$, with a surjective residue homomorphism onto the fibre function field whose kernel is the maximal ideal, compatible with the residue map of $A$ on constants, and with every nonzero element scalable by a constant into the integers with nonzero residue. Assume further (`hspec`) that every Laurent series $y$ over $A$ whose coefficientwise image in `LaurentSeries (AlgebraicClosure ℚ)` lies in `modularFunctionFieldBar N` is $R$-integral, with $R$-residue equal, as a Laurent series over $k$, to the coefficientwise reduction of $y$. Let $P$ be a place of `modularFunctionFieldBar N` over the algebraic closure of $\mathbb{Q}$ (a proper valuation subring containing the constants and a principal ideal ring) such that for some $a \in A$ the element `jBar N` $- a$ lies in the nonunits of $P$, and let $Q$ be a place of `modularFunctionFieldC k N` over $k$. If, for every element $h$ of `R.integers` that is integral over the subalgebra generated over the algebraic closure of $\mathbb{Q}$ by `jBar N`, and every $a \in A$ with $h - a$ in the nonunits of $P$, the difference of the $R$-residue of $h$ and the image of the residue of $a$ lies in the nonunits of $Q$, then the specialisation `fm.spPlace` of $P$ (formed with the surjectivity of the residue map, `dataAll` and the separability hypothesis) equals $Q$.
--
--   This is the rigidity half of the theory of reduction of places of the modular function field modulo a prime divisor of $\overline{\mathbb{Q}}$: the reduction relation imposed at those $R$-integral functions which are integral over $\overline{\mathbb{Q}}[j]$ determines the specialised place uniquely, so any place satisfying it coincides with `fm.spPlace P`. It is used by [`ModularCurve.CharPModel.FibreModel.spPlace_eq`](thm.html#ModularCurve.CharPModel.FibreModel.spPlace_eq) and by [`ModularCurve.PlaceSpecialization.sp_eq_spPlace_of_isModel_of_orderLawFixed`](thm.html#ModularCurve.PlaceSpecialization.sp_eq_spPlace_of_isModel_of_orderLawFixed) to identify specialisations constructed by other means with the one produced from the fibre model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open AlgebraicCurve

theorem ModularCurve.CharPModel.FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ (IsLocalRing.ResidueField A)
      (IsLocalRing.residue A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)))).Separable)
    (R : AlgebraicCurve.RegularProlongation A (ModularCurve.modularFunctionFieldBar N)
      (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N))
    (hspec : ∀ (y : LaurentSeries A) (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar N),
      ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ : ModularCurve.modularFunctionFieldBar N) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N) :
            LaurentSeries (IsLocalRing.ResidueField A)) = ModularCurve.coeffMap (IsLocalRing.residue A) y)
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N))
    (hP : ∃ a : A, ModularCurve.CharPModel.jBar N -
        algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits)
    (Q : AlgebraicCurve.Place (IsLocalRing.ResidueField A)
      (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N))
    (hclause : ∀ h : R.integers,
      IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
          ({ModularCurve.CharPModel.jBar N} : Set (ModularCurve.modularFunctionFieldBar N)))
        (h : ModularCurve.modularFunctionFieldBar N) →
      ∀ a : A, (h : ModularCurve.modularFunctionFieldBar N) -
          algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits →
        R.residue h - algebraMap (IsLocalRing.ResidueField A)
            (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N) (IsLocalRing.residue A a) ∈
          Q.toValuationSubring.nonunits) :
    fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P = Q := by sorry
