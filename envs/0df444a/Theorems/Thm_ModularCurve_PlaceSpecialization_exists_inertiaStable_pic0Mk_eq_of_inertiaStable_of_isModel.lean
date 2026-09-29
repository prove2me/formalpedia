-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_inertiaStable_pic0Mk_eq_of_inertiaStable_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_inertiaStable_pic0Mk_eq_of_inertiaStable_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/1b78d4b0-1864-51eb-877f-51408fb4ab18
-- title:
--   Inertia-stable divisor classes with strict or supersingular support
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \neq 0$ with $q \nmid N$, and an algebraically closed field $k$ of characteristic $q$ together with a ring homomorphism $\mathrm{red} \colon A \to k$. Let `data` consist of a monic bivariate integral polynomial $\Phi$ of degree $\psi(q)$ annihilating the pair of $q$-expansions $(j, j_q)$, and let `hKr` assert the Kronecker congruence, that the reduction of $\Phi$ modulo $q$ equals $(\mathrm{C}(X)^q - X)(\mathrm{C}(X) - X^q)$; let `hα` and `hβ` assert that the two degeneracy inclusions `heckeAlphaBar` and `heckeBetaBar` of the level-$N$ function field over $\overline{\mathbb{Q}}$ into the level-$Nq$ one are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` for these data, so in particular a map `P.sp` from places of `modularFunctionFieldBar N` to places of `modularFunctionFieldC k N` and a homomorphism on degree-zero divisor classes, subject to the structure's compatibilities. Let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places (rational, affine-geometric, with value of the geometric $j$ in the supersingular $j$-set `ssJSet q k`). Let $R$ be a `ProlongationTuple` over $P$ which is a model (the two divisor laws and the two cusp laws), satisfies the regularity law at $W$, and satisfies the order law at places fixed by the square of Frobenius. Then for every degree-zero divisor $D_0$ of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$ that is fixed, as a divisor, by the arithmetic Galois action of every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$, there is a degree-zero divisor $D$ with the same class in $\mathrm{Pic}^0$, again fixed by every such $\sigma$, and such that every place $V$ in the support of $D$ is strict of the first kind (Frobenius on level-$N$ places over $k$ carries `P.reduceFst V` to `P.reduceSnd V`, while its square does not fix `P.reduceFst V`), or strict of the second kind (`P.reduceFst V` is the Frobenius image of `P.reduceSnd V`, while the square of Frobenius does not fix `P.reduceSnd V`), or satisfies `P.reduceFst V ∈ W`.
--
--   This is the divisor-moving step in the analysis of the special fibre of the modular curve of level $Nq$ at $q$: any inertia-stable degree-zero class can be represented by an inertia-stable divisor supported away from the places reducing to a non-supersingular point fixed by the square of Frobenius. It is the version with an arbitrary algebraically closed receiving field $k$ in place of the residue field of $A$, and it is used to produce inertia-fixed representatives with controlled support in [`ModularCurve.PlaceSpecialization.exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_inertiaStable_pic0Mk_eq_of_inertiaStable_of_isModel.lean

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

theorem ModularCurve.PlaceSpecialization.exists_inertiaStable_pic0Mk_eq_of_inertiaStable_of_isModel
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
      ∀ D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
        (∀ σ ∈ A.inertiaSubgroupIn ℚ,
          arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
            (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = D₀) →
        ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
          Pic0.mk D = Pic0.mk D₀ ∧
          (∀ σ ∈ A.inertiaSubgroupIn ℚ,
            arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
              (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = D) ∧
          (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
            P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) := by sorry
