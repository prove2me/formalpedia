-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_smul_mem_integers_of_isGoodDiv_of_admissible_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_smul_mem_integers_of_isGoodDiv_of_admissible_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/cd34d917-e63d-582e-8db8-5cc4119b8591
-- title:
--   Common Gauss normalisation on both prolongations at level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Let `data` be a datum consisting of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, let `hKr` assert the Kronecker congruence $\Phi \equiv (C X^q - X)(C X - X^q)$ modulo $q$, and let `hα`, `hβ` assert that the two degeneracy inclusions `heckeAlphaBar`, `heckeBetaBar` of level $1$ and $q$ over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a `PlaceSpecialization` for these data, and let $R$ be a `ProlongationTuple` over $P$, i.e. a pair of regular prolongations $R_1, R_2$ of $A$ to the level-$1\cdot q$ function field with residue fields in the geometric level-$1$ function field over $k$, together with the stated compatibilities. Assume `R.IsModel`, that is the two divisor laws and the two cusp laws for $R$ hold. Let $W$ be a finset of places of `modularFunctionFieldC k 1` whose elements are exactly the supersingular places `ssPlaces q 1 k` (rational, affine geometric, with value of the geometric $j$-generator in `ssJSet q k`), and assume the regularity law `R.RegularityLaw W`. Let $f \neq 0$ in `modularFunctionFieldBar (1 * q)` and let $D$ be the divisor with $D(V) = \operatorname{ord}_V(f)$ at every place $V$. Assume $D$ is good for $P$, i.e. every place in its support is strict on the first or on the second side, and assume the glue datum $P.\mathtt{glueData}$ attached to $D$ and to the finset of node pairs obtained from $W$ by the coefficientwise Frobenius semilinear automorphism `arithFrobC q k 1` is admissible: the two pushed-forward divisors $\mathrm{reduceFst}_*(D|_{\mathrm{IsStrictFst}})$ and $\mathrm{reduceSnd}_*(D|_{\mathrm{IsStrictSnd}})$ have degree zero and vanish, respectively, at the first and second components of each node pair. Then there exists $c \in \overline{\mathbb{Q}}$, $c \neq 0$, such that $c \cdot f$ lies in the valuation subrings $R_1.\mathtt{integers}$ and $R_2.\mathtt{integers}$ and its residues under $R_1$ and under $R_2$ are both nonzero.
--
--   This is the normalisation step which, for a principal divisor balanced between the two components of the reduction of $X_0(q)$ at $q$, produces a single scalar making the function simultaneously integral with nonvanishing reduction on both prolongations; it is the level-one case ($N = 1$, level $q$, two cusps $0$ and $\infty$) of the corresponding statement at auxiliary level $N$. It is used in the level-one computation of the divisors of the two residues as a sum of point classes on the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_smul_mem_integers_of_isGoodDiv_of_admissible_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_smul_mem_integers_of_isGoodDiv_of_admissible_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hDf : ∀ V, D V = V.ord f)
    (hgood : P.IsGoodDiv D)
    (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) D ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W)) :
    ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0)
      (h₁ : c • f ∈ R.R₁.integers) (h₂ : c • f ∈ R.R₂.integers),
      R.R₁.residue ⟨c • f, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨c • f, h₂⟩ ≠ 0 := by sorry
