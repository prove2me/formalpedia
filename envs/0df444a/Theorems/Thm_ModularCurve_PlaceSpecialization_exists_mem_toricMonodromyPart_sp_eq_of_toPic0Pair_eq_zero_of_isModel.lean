-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_mem_toricMonodromyPart_sp_eq_of_toPic0Pair_eq_zero_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_mem_toricMonodromyPart_sp_eq_of_toPic0Pair_eq_zero_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/1a0c187b-3aae-58ec-863a-0d32aac1a43d
-- title:
--   Glued classes killed by `toPic0Pair` lift to toric monodromy
-- statement:
--   Let $N$ be a nonzero natural number, $q$ a prime not dividing $N$, and $A$ a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, so that its residue field $\kappa =$ `ResidueField A` has characteristic $q$; $J^0(M)$ denotes `JZero M`, the degree-zero divisor class group $\mathrm{Pic}^0$ of the base-changed modular function field of level $M$ over $\overline{\mathbb{Q}}$, equipped with its Hecke-algebra module structure. The data are: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,\kappa\,N$ whose members are exactly the places satisfying `IsSupersingularPlace q N`; a hypothesis that the set $S = \{(w, \varphi \cdot w) : w \in W\}$ of node pairs, formed with the semilinear automorphism $\varphi = \mathrm{arithFrobC}$ induced by the $q$-power Frobenius of $\kappa$ on coefficients, is stable under $\varphi$; a bivariate modular polynomial datum $\mathrm{data}$ for $q$ together with the Kronecker congruence $\Phi \equiv (C(X)^q - X)(C(X) - X^q) \bmod q$; integrality of the two degeneracy embeddings $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ from level $N$ to level $Nq$; a place specialisation $P$ over the reduction $A \to \kappa$; a prolongation tuple $R$ for $P$ satisfying the model laws (the two divisor laws and the two cusp laws), the regularity law and node value law for $W$, and the order law at Frobenius-fixed affine places; a width function $e$ on places; an additive map $\mathrm{comp}$ from the inertia invariants $H = J^0(Nq)^{I_A}$ (elements fixed by the image $I_A$ of the inertia subgroup of $A$ over $\mathbb{Q}$) onto the component group of the width-weighted Gram map for $S$, whose kernel consists precisely of the classes that are good for $S$ in the sense of $P$; and an additive map $\mathrm{sp} : H \to \mathrm{GluedPic}^0(\kappa, S)$ which is a glued specialisation for $P$, that is, computes on good degree-zero divisors the class of $P$'s explicit gluing datum. The conclusion asserts: for every $g$ in $\mathrm{GluedPic}^0(\kappa, S)$ (the quotient of admissible gluing data — pairs of degree-zero divisors vanishing at the node places together with a family of scalars indexed by $S$ — by the glued principal data) with $\mathrm{toPic0Pair}\,g = 0$, and killed by some positive integer coprime to $q$, there exist $y$ in $\mathrm{toricMonodromyPart}\,q\,I_A$ — the Hecke-algebra span inside $J^0(Nq)$ of the differences $\sigma \cdot x - x$ with $\sigma \in I_A$ and $x$ killed by some positive integer coprime to $q$ — with $y \in H$ and $\mathrm{sp}\,y = g$.
--
--   This is the surjectivity half of the description of the toric part at the special fibre of $X_0(Nq)$ in characteristic $q$: every glued class whose pair of divisor classes on the two normalised components vanishes is specialised from an inertial monodromy difference of prime-to-$q$ torsion. It feeds the statement [`ModularCurve.PlaceSpecialization.exists_heckeModule_componentGroup_toricMonodromyPart_mem_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_heckeModule_componentGroup_toricMonodromyPart_mem_of_isModel), which combines it with the component-group map `comp`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_mem_toricMonodromyPart_sp_eq_of_toPic0Pair_eq_zero_of_isModel.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_mem_toricMonodromyPart_sp_eq_of_toPic0Pair_eq_zero_of_isModel (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
        (∀ g : GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W),
          GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) g = 0 →
            (∃ m : ℕ, 0 < m ∧ m.Coprime q ∧ m • g = 0) →
              ∃ y : ↥(toricMonodromyPart (J := JZero (N * q)) q (A.inertiaSubgroupIn ℚ)),
                ∃ hy : (y : JZero (N * q)) ∈ inertiaInvariants A (N * q),
                  sp ⟨(y : JZero (N * q)), hy⟩ = g) := by sorry
