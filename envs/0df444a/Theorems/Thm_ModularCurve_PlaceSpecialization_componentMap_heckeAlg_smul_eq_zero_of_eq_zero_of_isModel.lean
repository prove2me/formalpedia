-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_componentMap_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel
-- name    : ModularCurve.PlaceSpecialization.componentMap_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/5dce3c41-43a2-523a-8c40-72012c4bee9d
-- title:
--   Hecke stability of the kernel of the component map at q
-- statement:
--   Let $N$ be a nonzero natural number and $q$ a prime with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a nonunit of $A$; its residue field $\kappa = \mathrm{ResidueField}\,A$ then has characteristic $q$. Both $\mathrm{JZero}(Nq)$ and $\mathrm{JZero}(N)$, the degree-zero divisor class groups of the base-changed modular function fields $\mathrm{modularFunctionFieldBar}$, carry the Hecke-algebra module structure `heckeModuleBar`, where `HeckeAlg` is the polynomial ring $\mathbb{Z}[T_\ell : \ell \text{ prime}]$. The assertion is made for every finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,\kappa\,N$ over $\kappa$ whose members are exactly the supersingular places `ssPlaces q N κ`; every hypothesis `hstab` that the node pairs $(w, \mathrm{Frob}\cdot w)$, $w \in W$, associated with the arithmetic Frobenius semilinear automorphism `arithFrobC q κ N` form a set stable under that automorphism; every modular polynomial datum `data` for $q$ satisfying the Kronecker congruence `hKr`; every pair of integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy maps from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$; every place-specialization datum $P$ for $A, q, N$, `data`, `hKr`, $\kappa$ and the residue map $A \to \kappa$; every prolongation tuple $R$ over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and the node value law for $W$, and the order law at Frobenius-fixed affine places; every width function $e$ on places; and every pair of additive maps $\mathrm{comp}$ from the inertia invariants $\mathrm{JZero}(Nq)^{I_A}$ to the combinatorial component group of the widths `widthOfPlaces` and $\mathrm{sp}$ from the same group to the glued degree-zero class group $\mathrm{GluedPic0}$ of $(\kappa, \mathrm{modularFunctionFieldC}\,\kappa\,N)$ along the node pairs, such that $\mathrm{comp}$ is surjective, $\mathrm{comp}(x) = 0$ holds exactly when the class $x$ is a good class for the node pairs in the sense of `P.IsGoodClass`, and $\mathrm{sp}$ is a glued specialization for $P$. Under these hypotheses, for every $T \in$ `HeckeAlg` and every $x$ in the inertia invariants such that $T \cdot x$ again lies in the inertia invariants, $\mathrm{comp}(x) = 0$ implies $\mathrm{comp}(T \cdot x) = 0$.
--
--   This is the Hecke-equivariance of the kernel of the component map attached to the semistable reduction of $J_0(Nq)$ at a place over $q$: the good classes, identified with that kernel, are carried to good classes by every element of the full Hecke algebra. It is used in the construction of the toric monodromy part of the specialization and, through it, in the comparison of the character group of the special fibre at level $Nq$ with the level-$N$ data that underlies level lowering at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_componentMap_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
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

theorem ModularCurve.PlaceSpecialization.componentMap_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
        (∀ (T : HeckeAlg) (x : ↥(inertiaInvariants A (N * q)))
            (hx : T • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp x = 0 → comp ⟨T • (x : JZero (N * q)), hx⟩ = 0) := by sorry
