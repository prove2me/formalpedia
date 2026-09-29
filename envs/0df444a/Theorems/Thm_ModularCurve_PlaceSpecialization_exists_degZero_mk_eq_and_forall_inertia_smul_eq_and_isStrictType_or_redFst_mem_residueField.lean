-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_degZero_mk_eq_and_forall_inertia_smul_eq_and_isStrictType_or_redFst_mem_residueField
-- name    : ModularCurve.PlaceSpecialization.exists_degZero_mk_eq_and_forall_inertia_smul_eq_and_isStrictType_or_redFst_mem_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/0c1411d2-980b-5cac-8de8-4c7be9afce91
-- title:
--   Inertia-fixed admissible representatives of inertia-invariant classes in J₀(q)
-- statement:
--   Let $q$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $\kappa_A = \mathrm{ResidueField}\,A$ has characteristic $q$; fix modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on the pair of $q$-expansions $j, j_q$) together with a proof `hKr` that $\Phi$ reduces modulo $q$ to $(X^q - Y)(X - Y^q)$, and proofs `hα`, `hβ` that the two degeneracy embeddings $\bar\alpha, \bar\beta$ of the level-one function field over $\overline{\mathbb Q}$ into the level-$q$ one are integral. Let $P$ be a `PlaceSpecialization` of level one for $A$, $q$, these data and the residue map $A \to \kappa_A$, i.e. a reduction of places and of $\mathrm{Pic}^0$ from level one over $\overline{\mathbb Q}$ to level one over $\kappa_A$ compatible with $j$ and $j_N$; let $R$ be a `LevelOneProlongationPair` for $P$ — a pair of regular prolongations $R_1, R_2$ of $A$ to the level-$q$ function field, interchanged by the Fricke involution, with residue maps into the level-one function field over $\kappa_A$ — satisfying `IsModel` (the two divisor laws and the two cusp laws) and `OrderLawFixed`. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\ \kappa_A\ 1$ whose members are exactly the supersingular places (rational affine geometric places at which $j$ takes a supersingular value), and let $x$ lie in $\mathrm{inertiaInvariants}\,A\,(1 \cdot q)$, the subgroup of $\mathrm{Pic}^0$ of the level-$(1\cdot q)$ function field over $\overline{\mathbb Q}$ fixed by the arithmetic action of the inertia subgroup $A.\mathrm{inertiaSubgroupIn}\ \mathbb Q$. Then there is a degree-zero divisor $D$ with $\mathrm{Pic}^0$ class equal to $x$ such that every place $V$ in the support of $D$ is fixed by $\mathrm{arithmeticGalois}\ \sigma$ for all $\sigma$ in that inertia subgroup, and satisfies one of: $\mathrm{Frob}(P.\mathrm{redFst}\,V) = P.\mathrm{redSnd}\,V$ with $\mathrm{Frob}^2(P.\mathrm{redFst}\,V) \neq P.\mathrm{redFst}\,V$; or $P.\mathrm{redFst}\,V = \mathrm{Frob}(P.\mathrm{redSnd}\,V)$ with $\mathrm{Frob}^2(P.\mathrm{redSnd}\,V) \neq P.\mathrm{redSnd}\,V$; or $P.\mathrm{redFst}\,V \in W$, where $\mathrm{redFst}$ and $\mathrm{redSnd}$ are the specialisations of the restrictions of $V$ along $\bar\alpha$ and $\bar\beta$ and $\mathrm{Frob}$ is the geometric-level Frobenius on places attached to `data` and `hKr`.
--
--   This is the representability step underlying the description of the specialisation of an inertia-invariant point of $J_0(q)(\overline{\mathbb Q})$ to the component group of the Néron model at $q$: it produces a representing degree-zero divisor all of whose points are inertia-fixed and admissible, so that depths at the supersingular crossings of the two components of the special fibre of $X_0(q)$ can be read off. Stated here in the residue-field edition, where the target field is $\kappa_A$ itself and the reduction map is the residue map of $A$; it feeds the construction of the component homomorphism extension in [`ModularCurve.exists_componentHom_extension_of_dRModelPackage_of_abelJacobi_of_ffPin`](thm.html#ModularCurve.exists_componentHom_extension_of_dRModelPackage_of_abelJacobi_of_ffPin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_degZero_mk_eq_and_forall_inertia_smul_eq_and_isStrictType_or_redFst_mem_residueField.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_degZero_mk_eq_and_forall_inertia_smul_eq_and_isStrictType_or_redFst_mem_residueField
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (IsLocalRing.ResidueField A) q] [DecidableEq (IsLocalRing.ResidueField A)]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr (IsLocalRing.ResidueField A) (IsLocalRing.residue A) hα hβ)
    (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place (IsLocalRing.ResidueField A) (modularFunctionFieldC (IsLocalRing.ResidueField A) 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 (IsLocalRing.ResidueField A))
    (x : ↥(inertiaInvariants A (1 * q))) :
    ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))),
      Pic0.mk D = (x : JZero (1 * q)) ∧
      ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ,
            arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) ∧
          (P.IsStrictTypeOne V ∨ P.IsStrictTypeTwo V ∨ P.redFst V ∈ W) := by sorry
