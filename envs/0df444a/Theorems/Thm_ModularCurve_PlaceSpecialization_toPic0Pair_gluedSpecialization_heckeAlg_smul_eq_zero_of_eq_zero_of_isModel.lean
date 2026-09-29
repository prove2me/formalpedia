-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel
-- name    : ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/2282be2c-397a-5544-9bcf-ca006c38ce0e
-- title:
--   Hecke stability of the toric kernel of the glued specialization
-- statement:
--   Fix $N$ with $N \neq 0$ and a prime $q$ with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ (that is, $q$ is a non-unit of $A$), so that its residue field $\kappa = \mathrm{ResidueField}\,A$ has characteristic $q$; the groups $\mathrm{JZero}(Nq)$ and $\mathrm{JZero}(N)$ carry the Hecke action `heckeModuleBar` of `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$. Assume given: a finite set $W$ of places of the level-$N$ modular function field $F_N = \mathrm{modularFunctionFieldC}\,\kappa\,N$ consisting exactly of the supersingular places `ssPlaces q N κ`; stability of the set $S = \mathrm{nodePairsOfPlaces}(\mathrm{arithFrobC}\,q\,\kappa\,N)\,W$ of node pairs $(w, \mathrm{Frob}\cdot w)$ under the coefficientwise semilinear Frobenius $\mathrm{arithFrobC}\,q\,\kappa\,N$, in the sense that $(g\cdot s_1, g\cdot s_2) \in S$ for all $s \in S$; modular polynomial data $\mathrm{data}$ for $q$ satisfying the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q) \bmod q$; integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy inclusions $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ from level $N$ to level $Nq$; a place specialization datum $P$ for $A$, $q$, $N$, $\mathrm{data}$, with target field $\kappa$ and reduction $\mathrm{residue}\,A$; a prolongation tuple $R$ for $P$ which is a model (the two divisor laws together with the two cusp laws) and satisfies the regularity law and node value law for $W$ and the fixed-place order law; a width function $e$ on places of $F_N$; and additive maps $\mathrm{comp}$ and $\mathrm{sp}$ on the inertia invariants $\mathrm{JZero}(Nq)^{I_A}$ (classes fixed by the inertia subgroup of $A$ inside $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$), with values in the combinatorial component group of the widths $\mathrm{widthOfPlaces}$ and in the glued degree-zero class group $\mathrm{GluedPic0}\,\kappa\,F_N\,S$ respectively, such that $\mathrm{comp}$ is surjective, $\mathrm{comp}\,x = 0$ holds exactly when $x$ is a good class for $S$ (representable by a degree-zero divisor whose support is strictly of the first or second kind and whose glue datum is admissible), and $\mathrm{sp}$ is a glued specialization for $S$ (it sends the class of any such good degree-zero divisor to the class of its glue datum). The conclusion: for every Hecke element $T$ and every $x$ in the inertia invariants with $T \cdot x$ again in the inertia invariants, if $\mathrm{comp}\,x = 0$ and $\mathrm{toPic0Pair}_S(\mathrm{sp}\,x) = 0$, then $\mathrm{toPic0Pair}_S(\mathrm{sp}(T\cdot x)) = 0$, where $\mathrm{toPic0Pair}_S$ is the map from the glued group to the pair of $\mathrm{Pic}^0$'s induced by the two divisor components.
--
--   This is the Hecke-equivariance step in the analysis of the special fibre of $J_0(Nq)$ at $q$: the locus of good inertia-invariant classes whose glued specialization has trivial image in $\mathrm{Pic}^0 \times \mathrm{Pic}^0$ (the toric part, cut out by the gluing units) is stable under the whole Hecke algebra. It is used by the existence statements that assemble a width function, a component map and a glued specialization for a given place datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel.lean

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

theorem ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
            comp x = 0 →
              GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (sp x) = 0 →
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (sp ⟨T • (x : JZero (N * q)), hx⟩) = 0) := by sorry
