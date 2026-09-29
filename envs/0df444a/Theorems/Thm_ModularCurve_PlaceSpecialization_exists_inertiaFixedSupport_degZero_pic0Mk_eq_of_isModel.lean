-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/8552eed3-156c-51a1-977d-e44f311f46e6
-- title:
--   Inertia-fixed representative with strict or supersingular support
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \ge 1$ with $q \nmid N$, and an algebraically closed field $k$ of characteristic $q$ together with a ring homomorphism $\mathrm{red} : A \to k$. Let `data` be a modular polynomial datum for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions) satisfying the Kronecker congruence `hKr`, namely that $\Phi$ reduced modulo $q$ equals $(X^q - Y)(X - Y^q)$, and assume `hα`, `hβ`: the two degeneracy inclusions `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a place specialisation of level $N$ at $A$ over $k$ via $\mathrm{red}$, let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places `ssPlaces q N k`, and let $R$ be a prolongation tuple over $P$ which is a model (the two divisor laws and the two cusp laws), satisfies the regularity law at $W$, and satisfies the order law at Frobenius-fixed affine geometric places. Then every class $x$ in the degree-zero Picard group `JZero (N * q)` of the level-$Nq$ function field over $\overline{\mathbb{Q}}$ that is fixed by every element of the inertia subgroup of $A$ in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ is the class of a degree-zero divisor $D$ such that every $\sigma$ in that inertia subgroup, acting through `arithmeticGalois`, fixes each place $V$ of the support of $D$, and each such $V$ is strict of the first kind ($\mathrm{Frob}(P.\mathrm{reduceFst}\,V) = P.\mathrm{reduceSnd}\,V$ with $\mathrm{Frob}^2$ moving $P.\mathrm{reduceFst}\,V$), or strict of the second kind ($P.\mathrm{reduceFst}\,V = \mathrm{Frob}(P.\mathrm{reduceSnd}\,V)$ with $\mathrm{Frob}^2$ moving $P.\mathrm{reduceSnd}\,V$), or has $P.\mathrm{reduceFst}\,V \in W$.
--
--   This is the moving lemma underlying the computation of the component-group and inertia action on $J_0(Nq)$ at $q$: inertia-invariant classes are represented by divisors whose places individually survive the reduction, lying on one of the two components of the special fibre away from the supersingular crossings or else above a supersingular point. It feeds the construction of the depth and width data used in the description of the character group of the toric part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] (k : Type*) [Field k]
    [CharP k q] (red : A →+* k) (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
    (hO : R.OrderLawFixed) :
      ∀ x : ↥(inertiaInvariants A (N * q)),
        ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
          Pic0.mk D = (x : JZero (N * q)) ∧
          (∀ σ ∈ A.inertiaSubgroupIn ℚ,
            ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
              arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
          (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
            P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) := by sorry
