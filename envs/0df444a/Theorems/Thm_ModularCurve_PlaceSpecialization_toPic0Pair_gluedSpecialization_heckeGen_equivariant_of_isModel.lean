-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_heckeGen_equivariant_of_isModel
-- name    : ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_heckeGen_equivariant_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/fc00f411-46e3-5a6d-82e1-5bbb392a02df
-- title:
--   Hecke equivariance of the projected glued specialization at q
-- statement:
--   Fix $N$ with $N \neq 0$ and a prime $q$ with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, i.e. $q$ is a non-unit of $A$; its residue field $\kappa =$ `ResidueField A` then has characteristic $q$, and $J_0(M) =$ `JZero M` carries the Hecke-module structure `heckeModuleBar M` over `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$ for $M = N$ and $M = Nq$. The assertion is made for all data as follows: a finite set $W$ of places of the level-$N$ modular function field $F_N =$ `modularFunctionFieldC` $\kappa\, N$ over $\kappa$ whose members are exactly the supersingular places `ssPlaces q N` $\kappa$; the hypothesis that the finite set $\Sigma =$ `nodePairsOfPlaces` of pairs $(w, \varphi \cdot w)$, $w \in W$, where $\varphi =$ `arithFrobC q` $\kappa\, N$ is the coefficientwise arithmetic Frobenius semilinear automorphism, is stable under $\varphi$ acting on both coordinates; a monic bivariate integral modular polynomial datum `data` for $q$ satisfying the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q) \bmod q$; integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy maps from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$; a specialization $P$ (`PlaceSpecialization`) consisting of a map on places from level $N$ over $\overline{\mathbb{Q}}$ to level $N$ over $\kappa$ together with an additive map `P.spPic0` $: J_0(N) \to \mathrm{Pic}^0(\kappa, F_N)$ and the order compatibilities for $j$ and $j_N$; a prolongation tuple $R$ for $P$ which is a model (the two divisor laws and the two cusp laws), satisfies the regularity law and the node-value law for $W$, and satisfies the fixed-point order law; a width function $e$ on places; additive maps $\mathrm{comp}$ from the inertia invariants $H = J_0(Nq)^{I_A}$ to the combinatorial component group of the widths `widthOfPlaces` $\varphi\, W\, e$, and $\mathrm{sp}$ from $H$ to the glued degree-zero class group `GluedPic0` $\kappa\, F_N\, \Sigma$; a `HeckeAlg`-module structure on $\mathrm{Pic}^0(\kappa, F_N)$; the hypothesis that `P.spPic0` is equivariant for this structure; surjectivity of $\mathrm{comp}$; the identification of $\ker(\mathrm{comp})$ with the good classes, namely $\mathrm{comp}(x) = 0$ if and only if $x$ is the class of a degree-zero divisor $D$ each of whose support places is strictly of the first or of the second kind for $P$ and whose glue datum `P.glueData` $\Sigma\, D$ is admissible; and the hypothesis that $\mathrm{sp}$ computes this gluing formula, sending the class of such a good $D$ whose class lies in $H$ to the class of any admissible gluing datum equal to `P.glueData` $\Sigma\, D$. Under all of these, the conclusion is: for every prime $\ell$ with $\ell \nmid Nq$ and every $x \in H$ such that $X_\ell \cdot x$ again lies in $H$, if $\mathrm{comp}(x) = 0$ then the projection `GluedPic0.toPic0Pair` $\Sigma$, which sends the class of a gluing datum $(D_1, D_2, c)$ to the pair of classes $(\,[D_1], [D_2]\,)$, satisfies $$\nu(\mathrm{sp}(X_\ell \cdot x)) = X_\ell \cdot \nu(\mathrm{sp}(x)),$$ the action on the right being the given one on $\mathrm{Pic}^0(\kappa, F_N)$ taken coordinatewise.
--
--   This is the Hecke-equivariance step for the specialization of $J_0(Nq)$ at a place above $q$ onto the two $\mathrm{Pic}^0$ legs of the glued special fibre, the form of Ribet's comparison of Hecke actions at level $Nq$ and level $N$ used in level lowering at $q$. It is applied in the downstream statements that transport the Hecke action to the component group and to the fibre of the level-$N$ Hecke module, and in the existence statement packaging a specialization together with widths, component map and glued specialization.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_heckeGen_equivariant_of_isModel.lean

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

theorem ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_heckeGen_equivariant_of_isModel (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
      (modP : Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hmod :         (∀ (T : HeckeAlg) (y : JZero N), P.spPic0 (T • y) = T • P.spPic0 y))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
        (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q →
          ∀ (x : ↥(inertiaInvariants A (N * q)))
            (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp x = 0 →
              GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩) =
                heckeGen ℓ •
                  GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                    (sp x)) := by sorry
