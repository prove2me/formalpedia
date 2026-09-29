-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_decomposition_smul_eq_spPic0_smul
-- name    : ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_decomposition_smul_eq_spPic0_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/a4698a2b-87c0-5bdf-a553-6209d75c60e1
-- title:
--   Decomposition-group equivariance of the glued specialization's Pic⁰-pair
-- statement:
--   Fix a nonzero level $N$ and a prime $q$ with $q \nmid N$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a non-unit of $A$; write $k = \mathrm{ResidueField}\,A$, which then has characteristic $q$, and equip $J_0$ at levels $Nq$ and $N$ with their Hecke-algebra module structures. The data bound are: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,k\,N$ over $k$ whose members are exactly the supersingular places for $q$ (rational, affine geometric, with $\mathrm{jGeomGen}$-value in $\mathrm{ssJSet}\,q$); a hypothesis that the node-pair set $\mathrm{nodePairsOfPlaces}$ attached to the coefficient Frobenius $\mathrm{arithFrobC}\,q\,k\,N$ and $W$ is stable under that semilinear automorphism; modular polynomial data for $q$ satisfying the Kronecker congruence; integrality of the two degeneracy maps $\alpha,\beta$ at $(\overline{\mathbb{Q}}, N, q)$; a place specialization $P$ for $A$, $q$, $N$ with target $k$ and reduction the residue map; a width function $e$ on places; additive maps $\mathrm{comp}$ from the inertia invariants of $J_0(Nq)$ to the component group of the widths $\mathrm{widthOfPlaces}$, and $\mathrm{sp}$ from those invariants to $\mathrm{GluedPic0}$ of the node pairs; surjectivity of $\mathrm{comp}$; the condition that $\mathrm{comp}\,x = 0$ holds exactly when $x$ is a good class for $P$; and the condition that $\mathrm{sp}$ is a glued specialization for $P$. The conclusion asserts: for $\sigma$ in the decomposition subgroup of $A$ over $\mathbb{Q}$ and $x$ an inertia invariant whose translate $\sigma \cdot x$ is again an inertia invariant, if $\mathrm{comp}\,x = 0$ and the pair of $\mathrm{Pic}^0$-classes of $\mathrm{sp}\,x$ under $\mathrm{GluedPic0.toPic0Pair}$ equals $(P.\mathrm{spPic0}\,a, P.\mathrm{spPic0}\,b)$ for some $a, b \in J_0(N)$, then the corresponding pair for $\mathrm{sp}(\sigma \cdot x)$ equals $(P.\mathrm{spPic0}(\sigma \cdot a), P.\mathrm{spPic0}(\sigma \cdot b))$.
--
--   This is the decomposition-group equivariance of the two $\mathrm{Pic}^0$-components of the glued specialization, the semistable-reduction counterpart of Galois equivariance for the pair of copies of $J_0(N)$ glued along the supersingular points. It is one of the compatibilities packaged, for given witnesses, into the existence statement for the width function, the component map and the glued specialization, and is used by [`ModularCurve.exists_width_comp_sp`](thm.html#ModularCurve.exists_width_comp_sp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_decomposition_smul_eq_spPic0_smul.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_decomposition_smul_eq_spPic0_smul (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
          ∀ (x : ↥(inertiaInvariants A (N * q)))
            (hx : σ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp x = 0 → ∀ a b : JZero N,
              GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (sp x) = (P.spPic0 a, P.spPic0 b) →
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                    (sp ⟨σ • (x : JZero (N * q)), hx⟩)
                  = (P.spPic0 (σ • a), P.spPic0 (σ • b))) := by sorry
