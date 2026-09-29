-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_eq_of_primeToTorsion_of_componentMap_eq_zero_of_gluedSpecialization_eq
-- name    : ModularCurve.PlaceSpecialization.eq_of_primeToTorsion_of_componentMap_eq_zero_of_gluedSpecialization_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/a989d483-053f-5cca-a0fa-76212c8636f1
-- title:
--   Prime-to-q inertia-invariant classes with equal glued specialisation coincide
-- statement:
--   Fix a nonzero level $N$ and a prime $q$ with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a non-unit of $A$, so that its residue field $k = \mathrm{ResidueField}\,A$ has characteristic $q$; the Hecke-algebra module structures on $\mathrm{JZero}(Nq)$ and $\mathrm{JZero}(N)$ are those given by `heckeModuleBar`. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$ over $k$ whose members are exactly the supersingular places `ssPlaces q N k`, and assume the node-pair set $S =$ `nodePairsOfPlaces (arithFrobC q k N) W`, the image of $W$ under $w \mapsto (w, \mathrm{arithFrob}\cdot w)$, satisfies $(g\cdot s_1, g\cdot s_2) \in S$ for all $s \in S$, where $g =$ `arithFrobC q k N` is the semilinear automorphism induced by the Frobenius of $k$. Let `data` be a `ModularPolynomialData q`, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions, subject to the Kronecker congruence $\Phi \bmod q = (X^q - Y)(X - Y^q)$; let $h\alpha$, $h\beta$ assert integrality of the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$. Let $P$ be a `PlaceSpecialization` for $A$, $q$, $N$, `data` and the residue map $A \to k$, and $R$ a `ProlongationTuple` over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and the node-value law for $W$, and the order law at fixed places. Let $e$ assign a natural number to each place, let $\mathrm{comp}$ be a surjective additive map from the inertia invariants $\mathrm{JZero}(Nq)^{I_A}$ (classes fixed by the inertia subgroup of $A$ over $\mathbb{Q}$) onto the component group of the width function `widthOfPlaces (arithFrobC q k N) W e`, whose kernel consists precisely of the classes that are good for $S$ in the sense of $P$ (representable by a degree-zero divisor supported on strictly-first or strictly-second places whose glued data is admissible), and let $\mathrm{sp}$ be an additive map from $\mathrm{JZero}(Nq)^{I_A}$ to $\mathrm{GluedPic0}\,k\,(\mathrm{modularFunctionFieldC}\,k\,N)\,S$ which is a glued specialisation for $P$. Then for all $a, b \in \mathrm{JZero}(Nq)^{I_A}$ whose images in $\mathrm{JZero}(Nq)$ are prime-to-$q$ torsion (killed by some $n > 0$ with $q \nmid n$), if $\mathrm{comp}\,a = \mathrm{comp}\,b = 0$ and $\mathrm{sp}\,a = \mathrm{sp}\,b$, then $a = b$.
--
--   This is the difference form of the injectivity of specialisation on the prime-to-$q$ part: on the identity component, the glued special-fibre class separates inertia-invariant classes of order prime to the residue characteristic. It is the shape in which the injectivity statement is consumed when two classes, such as $U_q(\varphi x)$ and $q\,x$ for a toric torsion class $x$ and a Frobenius element $\varphi$, have been shown to have the same glued specialisation and to lie in the kernel of the component map; it feeds the analysis of the Néron model of $J_0(Nq)$ at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_eq_of_primeToTorsion_of_componentMap_eq_zero_of_gluedSpecialization_eq.lean

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

theorem ModularCurve.PlaceSpecialization.eq_of_primeToTorsion_of_componentMap_eq_zero_of_gluedSpecialization_eq (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
        ∀ (a b : ↥(inertiaInvariants A (N * q))),
          PrimeToTorsion q (a : JZero (N * q)) → PrimeToTorsion q (b : JZero (N * q)) →
            comp a = 0 → comp b = 0 → sp a = sp b → a = b := by sorry
