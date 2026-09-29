-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isGoodClass_iff_isGluedSpecialization_of_not_genusFF_pos
-- name    : ModularCurve.PlaceSpecialization.exists_isGoodClass_iff_isGluedSpecialization_of_not_genusFF_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/acef1eda-05c6-528f-932f-ec6c112c2beb
-- title:
--   Genus-zero transfer of good-class and glued-specialization data
-- statement:
--   Fix $N \ge 1$ and a prime $q$ with $q \nmid N$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a non-unit of $A$, so that $k := \mathrm{ResidueField}(A)$ has characteristic $q$. Let $W$ be a finite set of places of the level-$N$ modular function field $\mathrm{modularFunctionFieldC}\ k\ N$ whose members are exactly the supersingular places for $q$ at level $N$, and assume the set of node pairs $\{(w,\ \mathrm{arithFrobC}\ q\ k\ N \cdot w) : w \in W\}$ is stable under the arithmetic Frobenius semilinear automorphism. Let `data` be modular polynomial data at $q$ (a monic $\Phi$ of degree $\psi(q)$ annihilating the pair of $q$-expansions of $j$) satisfying the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q) \bmod q$, and let the two Hecke degeneracy maps $\alpha, \beta$ from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$ be integral. Let $P$ be a place specialization over $A$ at $q$ and level $N$ with residue target $k$ and reduction map the residue map of $A$, carrying a prolongation tuple $R$ which is a model (the two divisor laws and the two cusp laws) and satisfies the order law at the Frobenius-fixed affine places. Let $e$ be a width function on places, let $\mathrm{comp}$ be an additive map from the inertia invariants of $J_0(Nq) = \mathrm{Pic}^0$ of the level-$Nq$ function field over $\overline{\mathbb{Q}}$ to the combinatorial component group attached to the widths of the node pairs of $W$, and let $\mathrm{sp}$ be an additive map from those inertia invariants to the glued $\mathrm{Pic}^0$ of the node pairs. Assume the kernel of $\mathrm{comp}$ consists exactly of the classes good for $P$ (represented by a degree-zero divisor all of whose support places are strictly first or strictly second for $P$, with admissible glue datum), and that $\mathrm{sp}$ is a glued specialization for $P$. Then, if $\mathrm{genusFF}\ k$ of the level-$N$ function field is not positive, there exists a place specialization $P_0$ on the same data for which $\mathrm{comp}$ has the same kernel description, for which the same $\mathrm{sp}$ is a glued specialization, and which admits a prolongation tuple $R_0$ that is a model and satisfies the regularity law on $W$, the node-value law on $W$ and the order law at the fixed places.
--
--   This is the upgrading step in the genus-zero case of the analysis of the special fibre of $X_0(Nq)$ at $q$: an arbitrary place specialization equipped with a model tuple satisfying the order law is replaced by one whose tuple satisfies in addition the regularity law and the node-value law on the supersingular places, without disturbing the component-group kernel description or the glued specialization already in hand. It feeds the comparison of the Hecke correspondence with the glued specialization at non-fixed nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_isGoodClass_iff_isGluedSpecialization_of_not_genusFF_pos.lean

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

set_option Elab.async false
open IsLocalRing ModularCurve
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.exists_isGoodClass_iff_isGluedSpecialization_of_not_genusFF_pos
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
      ¬ (0 < genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) →
      ∃ (P₀ : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        (∀ x : ↥(inertiaInvariants A (N * q)),
          comp x = 0 ↔ P₀.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q))) ∧
        P₀.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
          sp ∧
        ∃ R₀ : PlaceSpecialization.ProlongationTuple P₀,
          R₀.IsModel ∧ R₀.RegularityLaw W ∧ R₀.NodeValueLaw W ∧ R₀.OrderLawFixed := by sorry
