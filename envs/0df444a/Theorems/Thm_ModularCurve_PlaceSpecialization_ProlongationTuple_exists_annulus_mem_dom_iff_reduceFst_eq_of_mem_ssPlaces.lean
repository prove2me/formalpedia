-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulus_mem_dom_iff_reduceFst_eq_of_mem_ssPlaces
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulus_mem_dom_iff_reduceFst_eq_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/f984029b-b8e5-5427-a721-61f816b28d49
-- title:
--   Inertia-invariant annulus over a supersingular node of X₀(Nq)
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data $data$ for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ killing the pair of $q$-expansions) together with a proof $hKr$ that $\Phi$ reduces mod $q$ to $(Y^q-X)(Y-X^q)$, integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of level $N$ into level $Nq$, a place specialisation $P$ for these data, and a prolongation tuple $R$ over $P$, consisting of reductions `redBar`, `ι` and two regular prolongations $R_1$, $R_2$ of $A$ in $\overline{\mathbb Q}(X_0(Nq))$ linked by the Atkin–Lehner involution. Assume $q \nmid N$, that $R$ is a model (the two divisor laws and the two cusp laws), that $W_0$ is a finite set of places of the characteristic-$q$ level-$N$ function field all of which are supersingular (rational, affine as geometric places, with $j$-value in the supersingular set), that $R$ satisfies the regularity law and the node-value law for $W_0$ and the order law at frobenius-fixed affine places, and let $w \in W_0$. Then there is an annulus $An$ for $A$ in $\overline{\mathbb Q}(X_0(Nq))$, that is, a set $An.dom$ of places, a parameter $An.param$ and a modulus $An.modulus$ in the maximal ideal of $A$ satisfying the annulus axioms, such that: $An.dom$ consists exactly of those places $W$ whose first reduction $P.reduceFst\,W$ equals $w$ and which are strict on neither side (neither `P.IsStrictFst` nor `P.IsStrictSnd` holds); the modulus is nonzero; every $\sigma$ in the inertia subgroup of $A$ over $\mathbb Q$ fixes $An.param$ through `arithmeticGalois`; the product of the image of $An.modulus^{-1}$ with $An.param$ lies in the valuation subring $R.R_1.integers$; and $An.param$ lies in $R.R_2.integers$ with nonzero image under $R.residue_2$.
--
--   This supplies, at every level $N$ prime to $q$, the annulus description of the formal neighbourhood of a supersingular point of the fibre at $q$ of $X_0(Nq)$: the tube of places reducing to a given supersingular node carries a parameter invariant under inertia at $A$, integral for the second prolongation with nonzero residue and integral after division by the modulus for the first. It is used in [`ModularCurve.PlaceSpecialization.exists_goodRep_admissible_smul_single_sub_self_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_goodRep_admissible_smul_single_sub_self_of_isModel), where the local equation of the inertial displacement over the node is read off from such an annulus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulus_mem_dom_iff_reduceFst_eq_of_mem_ssPlaces.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulus_mem_dom_iff_reduceFst_eq_of_mem_ssPlaces
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel)
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) (hW₀ : ∀ v ∈ W₀, v ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W₀) (hval : R.NodeValueLaw W₀) (hO : R.OrderLawFixed)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W₀) :
    ∃ An : Annulus A ↥(modularFunctionFieldBar (N * q)),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        W ∈ An.dom ↔ (P.reduceFst W = w ∧ ¬ P.IsStrictFst W ∧ ¬ P.IsStrictSnd W)) ∧
      ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((An.modulus : AlgebraicClosure ℚ))⁻¹
          * An.param ∈ R.R₁.integers ∧
      ∃ h₂ : An.param ∈ R.R₂.integers, R.residue₂ ⟨An.param, h₂⟩ ≠ 0 := by sorry
