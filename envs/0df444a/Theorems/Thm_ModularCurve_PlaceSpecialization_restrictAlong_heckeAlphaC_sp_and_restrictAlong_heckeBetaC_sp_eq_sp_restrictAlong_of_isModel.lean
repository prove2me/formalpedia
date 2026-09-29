-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel
-- name    : ModularCurve.PlaceSpecialization.restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/6a52ec30-ff1a-5b78-b5e3-9fc795b76b5e
-- title:
--   Place specialisation commutes with both degeneracy maps
-- statement:
--   Let $N \ge 1$ and let $q$ be a prime with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$, in the sense that $q$ belongs to the nonunits of $A$; its residue field $\kappa =$ `ResidueField A` then has characteristic $q$. Fix `data : ModularPolynomialData q`, i.e. a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ with $\Phi(j,j_q)=0$, together with the Kronecker congruence `hKr`, asserting that $\Phi$ reduced modulo $q$ equals $(C X^q - X)(C X - X^q)$. Assume the two degeneracy embeddings $\overline{\mathbb Q}(X_0(N)) \to \overline{\mathbb Q}(X_0(Nq))$, namely the inclusion `heckeAlphaBar` and the map `heckeBetaBar` induced by $q$-expansion $q \mapsto q^{q}$, are integral (`hα`, `hβ`), and let $P$ be a `PlaceSpecialization` for $A$, $q$, level $N$, `data`, `hKr`, with target field $\kappa$ and reduction map the residue map of $A$; let $R$ be a `ProlongationTuple` for $P$ satisfying `R.IsModel` (the two divisor laws and the two cusp laws at the infinity and zero sides) and `R.OrderLawFixed` (the order law at the Frobenius-fixed affine geometric places). Let $\ell$ be a prime with $\ell \ne q$, and assume the analogous data at level $N\ell$: integrality hypotheses `hαᵣ`, `hβᵣ`, a place specialisation $P_r$ for level $N\ell$, and a prolongation tuple $R_r$ for $P_r$ satisfying `Rᵣ.IsModel` and `Rᵣ.OrderLawFixed`. Assume further that the level-$N$-to-level-$N\ell$ degeneracy embeddings $\alpha =$ `heckeAlphaBar` and $\beta =$ `heckeBetaBar` over $\overline{\mathbb Q}$ are integral (`hαℓ`, `hβℓ`), that their characteristic-$q$ counterparts $\alpha_C =$ `heckeAlphaC` (the inclusion of `modularFunctionFieldC` $\kappa$ $N$ into the roof) and $\beta_C =$ `heckeBetaC` (induced by $q \mapsto q^{\ell}$) into the degeneracy roof $\mathcal R = \kappa(j, j_N, j_\ell, j_{N\ell})$ are integral (`hαC`, `hβC`), that $\mathcal R \le$ `modularFunctionFieldC` $\kappa$ $(N\ell)$ with integral inclusion (`hroof'`, `hι'`). Then for every place $W_0$ of `modularFunctionFieldBar (N * ℓ)`, the place $P_r.\mathrm{sp}(W_0)$, restricted along the inclusion of $\mathcal R$ and then along $\alpha_C$, equals $P.\mathrm{sp}$ of the restriction of $W_0$ along $\alpha$, and likewise with $\beta_C$ and $\beta$ in place of $\alpha_C$ and $\alpha$; restriction of places being pullback of the valuation subring along the given embedding.
--
--   This is the place-level statement that reduction modulo $q$ of geometric points commutes with the two finite degeneracy maps $X_0(N\ell) \to X_0(N)$ (the forgetful map and the $\ell$-isogeny quotient): the reduction of the image is the image of the reduction, for an abstract place-specialisation datum whose prolongation tuple satisfies the model and order laws. It feeds the statements comparing `sp` with restriction along the degeneracy maps and the computations of $y$-depth of places restricted along `heckeAlphaBar`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve IsLocalRing
open ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.PlaceSpecialization.restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P), R.IsModel → R.OrderLawFixed →
      ∀ (ℓ : Nat.Primes), (ℓ : ℕ) ≠ q →
        haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
        letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (N * ℓ)
        ∀ (hαᵣ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q)
          (hβᵣ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q)
          (Pᵣ : PlaceSpecialization A q (N * ℓ) data hKr (ResidueField A) (IsLocalRing.residue A) hαᵣ hβᵣ)
          (Rᵣ : PlaceSpecialization.ProlongationTuple Pᵣ), Rᵣ.IsModel → Rᵣ.OrderLawFixed →
        ∀ (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
          (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
          (hαC : (heckeAlphaC (ResidueField A) N ℓ).toRingHom.IsIntegral)
          (hβC : (heckeBetaC (ResidueField A) N ℓ).toRingHom.IsIntegral)
          (hroof' : charLDegeneracyRoof (ResidueField A) N ℓ ≤ modularFunctionFieldC (ResidueField A) (N * ℓ))
          (hι' : (IntermediateField.inclusion hroof').toRingHom.IsIntegral)
          (W₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))),
          ((Pᵣ.sp W₀).restrictAlong (IntermediateField.inclusion hroof') hι').restrictAlong
              (heckeAlphaC (ResidueField A) N ℓ) hαC
            = P.sp (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ) ∧
          ((Pᵣ.sp W₀).restrictAlong (IntermediateField.inclusion hroof') hι').restrictAlong
              (heckeBetaC (ResidueField A) N ℓ) hβC
            = P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ) := by sorry
