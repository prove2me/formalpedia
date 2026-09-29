-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_pic0Mk_eq_zero_of_isGoodDiv_of_mk_glueData_eq_zero_of_nsmul_eq_zero_of_isModel
-- name    : ModularCurve.PlaceSpecialization.pic0Mk_eq_zero_of_isGoodDiv_of_mk_glueData_eq_zero_of_nsmul_eq_zero_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/5b7d616a-97a9-5a88-9a27-f8665c533d65
-- title:
--   Prime-to-q torsion trivial on the glued reduction vanishes
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions) satisfying the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q)$ mod $q$, and integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings of the level-$N$ into the level-$Nq$ function field over $\overline{\mathbb Q}$. Let $P$ be a place specialization of this data, carrying a map `sp` from places of $\overline{\mathbb Q}$-level-$N$ modular function field to places of $X_0(N)$ over $k$ together with its compatibilities, and assume $q \nmid N$. Let $W$ be a finite set of places of the level-$N$ function field over $k$ whose members are exactly the supersingular places (rational, affine, with $j$-value in the supersingular set), and put $S = \{(w, \mathrm{arithFrob}_q\, w) : w \in W\}$, the node pairs formed with the coefficientwise $q$-power Frobenius automorphism. Let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and the node-value law at $W$, and the order law at the places fixed by the square of the geometric Frobenius on places. Let $D$ be a degree-zero divisor on the level-$Nq$ function field over $\overline{\mathbb Q}$ such that every place in the support of $D$ is strict of the first or of the second kind, such that the glue datum $(\mathrm{reduceFst}_*(D|_{\text{strict fst}}),\ \mathrm{reduceSnd}_*(D|_{\text{strict snd}}),\ 1)$ is admissible for $S$ (both divisors of degree zero, and vanishing at the first, resp. second, coordinates of the pairs in $S$) and has trivial class in the glued degree-zero class group `GluedPic0 S`. If $n \neq 0$, $q \nmid n$ and $n \cdot [D] = 0$ in $\mathrm{Pic}^0$, then $[D] = 0$.
--
--   This is the divisor-level form of the statement that the kernel of reduction of $J_0(Nq)$ at $q$ — whose special fibre is two copies of $X_0(N)$ over $k$ glued at the supersingular points — contains no torsion of order prime to $q$. It is used in the proof that, for classes of order prime to $q$, the difference $\sigma[D] - [D]$ lies in the inertia invariants, and thus in the study of the Galois action on the $q$-torsion of $J_0(Nq)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_pic0Mk_eq_zero_of_isGoodDiv_of_mk_glueData_eq_zero_of_nsmul_eq_zero_of_isModel.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.pic0Mk_eq_zero_of_isGoodDiv_of_mk_glueData_eq_zero_of_nsmul_eq_zero_of_isModel
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
    (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W)
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W))
    (hmk : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W)
        ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k N) W)
          (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩ = 0)
    (n : ℕ) (hn : n ≠ 0) (hqn : ¬ q ∣ n) (hnD : n • Pic0.mk D = 0) :
    Pic0.mk D = 0 := by sorry
