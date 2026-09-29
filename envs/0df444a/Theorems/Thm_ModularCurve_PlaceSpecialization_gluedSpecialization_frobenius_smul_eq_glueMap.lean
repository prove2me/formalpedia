-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_gluedSpecialization_frobenius_smul_eq_glueMap
-- name    : ModularCurve.PlaceSpecialization.gluedSpecialization_frobenius_smul_eq_glueMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/0ff29d03-fa70-5e56-97e1-4f8ce5930cdc
-- title:
--   Frobenius law for the glued specialization
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $q$ with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a nonunit of $A$; consequently the residue field $k = \mathrm{ResidueField}\,A$ has characteristic $q$, and $\mathrm{JZero}(Nq)$ and $\mathrm{JZero}(N)$ carry their Hecke-algebra module structures. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$ over $k$ whose members are exactly the supersingular places `ssPlaces q N k` (rational, affine geometric places at which the geometric $j$-generator takes a value in `ssJSet q k`), and assume (`hstab`) that the semilinear automorphism $g =$ `arithFrobC q k N`, induced coefficientwise by $x \mapsto x^q$ on $k$, is node-stable for the finite set `nodePairsOfPlaces g W` of pairs $(w, g \cdot w)$ with $w \in W$, i.e. applying $g$ to both entries of a pair in that set yields again a pair in it. Let `data` be modular polynomial data for $q$ satisfying the Kronecker congruence $\Phi \equiv (C(X)^q - X)(C(X) - X^q) \pmod q$, let $h\alpha$, $h\beta$ assert integrality of the two degeneracy maps `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$, and let $P$ be a `PlaceSpecialization` for $A$, $q$, $N$, these data and the residue map $A \to k$. Let $e$ be a width function on places, and let $\mathrm{comp}$ and $\mathrm{sp}$ be additive homomorphisms from the inertia invariants of $\mathrm{JZero}(Nq)$, that is the classes fixed by the inertia subgroup of $A$ over $\mathbb{Q}$, to the component group of the widths `widthOfPlaces g W e` and to $\mathrm{GluedPic}^0$ of $k$ and $\mathrm{modularFunctionFieldC}\,k\,N$ for the node pairs respectively, such that $\mathrm{comp}$ is surjective, $\mathrm{comp}\,x = 0$ holds exactly when $x$ is a good class for $P$ relative to the node pairs, and $\mathrm{sp}$ is a glued specialization for $P$ relative to the node pairs. The conclusion: for every automorphism $\varphi$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ that is a Frobenius at $A$ for $q$ (it lies in the decomposition subgroup of $A$ and acts as $x \mapsto x^q$ on $k$), every inertia-invariant $x$ such that $\varphi \cdot x$ is again inertia-invariant, and $\mathrm{comp}\,x = 0$, the value of $\mathrm{sp}$ at $\varphi \cdot x$ equals the image of $\mathrm{sp}\,x$ under the map `GluedPic0.glueMap` on glued Picard groups induced by `arithFrobC q k N` together with `hstab`.
--
--   This is the Frobenius-equivariance clause of the semistable specialization package at level $Nq$: on the part of the inertia invariants that dies in the component group, the glued specialization intertwines the action of a Frobenius element at $A$ with the gluing map induced by the arithmetic Frobenius on the supersingular node pairs. It is stated for given witnesses of the place specialization, the widths, the component map and the glued specialization, the same hypothesis telescope being shared by the other clauses of the package, and it is used in deriving the corresponding Frobenius and component-map compatibilities for the specialization of $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_gluedSpecialization_frobenius_smul_eq_glueMap.lean

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

theorem ModularCurve.PlaceSpecialization.gluedSpecialization_frobenius_smul_eq_glueMap (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
        (∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ q →
          ∀ (x : ↥(inertiaInvariants A (N * q)))
            (hx : φ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp x = 0 →
              sp ⟨φ • (x : JZero (N * q)), hx⟩ =
                GluedPic0.glueMap (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (arithFrobC q (ResidueField A) N) hstab (sp x)) := by sorry
