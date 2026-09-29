-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isNodeStable_isGoodClass_iff_isGluedSpecialization_glueMap_of_not_genusFF_pos
-- name    : ModularCurve.PlaceSpecialization.exists_isNodeStable_isGoodClass_iff_isGluedSpecialization_glueMap_of_not_genusFF_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/3a91d06f-f4f1-5b28-bb7d-7cd5d01845e0
-- title:
--   Genus-zero transport of glued specialisation data along a node-stable automorphism
-- statement:
--   Let $q$ be a prime and $N\ge 1$ with $q\nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a non-unit of $A$; then the residue field $k=\mathrm{ResidueField}\,A$ has characteristic $q$. Fix a finite set $W$ of places of the level-$N$ modular function field $\mathrm{modularFunctionFieldC}\,k\,N$ over $k$ whose members are exactly the supersingular places $\mathrm{ssPlaces}\,q\,N\,k$, and assume the node-pair set $\mathrm{nodePairsOfPlaces}$ obtained from $W$ by $w\mapsto(w,\,\mathrm{arithFrobC}\cdot w)$ is stable under the coefficientwise Frobenius semilinear automorphism $\mathrm{arithFrobC}\,q\,k\,N$. Fix modular polynomial data at $q$, that is a monic polynomial $\Phi$ in two variables over $\mathbb{Z}$ of degree $\psi(q)$ annihilating the pair of $q$-expansions, satisfying the Kronecker congruence that $\Phi$ reduces modulo $q$ to the product of $Y^{q}-X$ with $Y-X^{q}$, together with integrality of the two degeneracy embeddings $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$. Let $P$ be a place specialisation for these data with reduction map the residue map of $A$, carrying a prolongation tuple $R$ that is a model (the two divisor laws and the two cusp laws) and satisfies the order law at the Frobenius-fixed affine places. Let $e$ be a width function on places, let $\mathrm{comp}$ be an additive map from the inertia invariants of $\mathrm{JZero}(Nq)$ (classes fixed by the inertia subgroup of $A$ over $\mathbb{Q}$) to the component group of the widths $\mathrm{widthOfPlaces}$, and let $\mathrm{sp}$ be an additive map from those invariants to the glued Picard group $\mathrm{GluedPic0}$ of the node pairs, such that $\mathrm{comp}\,x=0$ holds precisely when $x$ is a good class for $P$, and $\mathrm{sp}$ is a glued specialisation for $P$. Assuming $\mathrm{genusFF}\,k\,(\mathrm{modularFunctionFieldC}\,k\,N)$ is not positive, there exist a place specialisation $P_0$ for the same data and a semilinear automorphism $g$ of the level-$N$ function field over $k$ stabilising the node pairs, such that the kernel condition for $\mathrm{comp}$ also characterises the good classes of $P_0$, the composite of $\mathrm{sp}$ with the endomorphism $\mathrm{GluedPic0.glueMap}$ induced by $g$ is a glued specialisation for $P_0$, and $P_0$ admits a prolongation tuple $R_0$ which is a model and satisfies the regularity law for $W$, the node value law for $W$ and the order law at fixed places.
--
--   This is the genus-zero case of the comparison step that upgrades a place specialisation already known to be a model with a fixed-place order law to one that in addition satisfies the regularity and node value laws, while transporting the component-group kernel description and the glued specialisation along a node-stable semilinear automorphism of the level-$N$ function field. It feeds the construction of matrices of glued specialisations attached to Hecke generators, used in the analysis of the special fibre of $J_0(Nq)$ at $q$ and its component group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_isNodeStable_isGoodClass_iff_isGluedSpecialization_glueMap_of_not_genusFF_pos.lean

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

theorem ModularCurve.PlaceSpecialization.exists_isNodeStable_isGoodClass_iff_isGluedSpecialization_glueMap_of_not_genusFF_pos
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
      ∃ (P₀ : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
        (g : SemilinearAut (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
        (hg : SemilinearAut.IsNodeStable (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) g),
        (∀ x : ↥(inertiaInvariants A (N * q)),
          comp x = 0 ↔ P₀.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q))) ∧
        P₀.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
          ((GluedPic0.glueMap (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) g hg).comp sp) ∧
        ∃ R₀ : PlaceSpecialization.ProlongationTuple P₀,
          R₀.IsModel ∧ R₀.RegularityLaw W ∧ R₀.NodeValueLaw W ∧ R₀.OrderLawFixed := by sorry
