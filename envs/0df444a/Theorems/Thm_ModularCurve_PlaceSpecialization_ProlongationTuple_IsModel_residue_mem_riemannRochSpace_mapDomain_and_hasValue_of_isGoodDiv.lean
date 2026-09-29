-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/5852013e-cce9-5f71-a82a-a64baaa6e418
-- title:
--   Residues of good-divisor sections and their node values
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q) \bmod q$, and hypotheses $h\alpha$, $h\beta$ asserting that the two degeneracy maps $\overline{\mathbb Q}$-embedding the level-$N$ function field into the level-$Nq$ one are integral; let $P$ be a place specialization of these data, and assume $q \nmid N$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$ whose members are exactly the supersingular places (rational, affine geometric, with $j$-value in the supersingular $j$-set for $q$), and let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (the two one-sided divisor laws off the $\varphi^2$-fixed places, together with the two cusp laws), the regularity and node-value laws at $W$, and the fixed-order law at affine $\varphi^2$-fixed places. Let $D \ge 0$ be a divisor on the level-$Nq$ function field over $\overline{\mathbb Q}$ all of whose support points are strict of the first or of the second kind, and let $G$ lie in the Riemann–Roch space $L(D)$, i.e. $v(G) \le \exp(D v)$ for every place $v$, and in the integers of both prolongations $R.R_1$, $R.R_2$. Then the first residue of $G$ lies in the Riemann–Roch space of the push-forward along $P.\mathrm{reduceFst}$ of the strict-first-kind part of $D$, the second residue lies in the Riemann–Roch space of the push-forward along $P.\mathrm{reduceSnd}$ of the strict-second-kind part, and for every $w \in W$ there is $c \in k$ such that the first residue has value $c$ at $w$ and the second residue has value $c$ at the translate of $w$ by the coefficientwise arithmetic Frobenius semilinear automorphism $\mathrm{arithFrobC}\,q\,k\,N$.
--
--   This is the reduction step for linear systems on the two-component special fibre of $X_0(Nq)$ at $q$: a section of $L(D)$ for a divisor supported at strict points reduces to a pair of sections with the expected pole bounds on the two copies of $X_0(N)_{/k}$, agreeing at the supersingular nodes. It is the engine behind the three subsequent statements that produce sections with prescribed residue pairs, linearly independent such pairs, and Galois-equivariant versions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.residue_mem_riemannRochSpace_mapDomain_and_hasValue_of_isGoodDiv
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : 0 ≤ D) (hgood : P.IsGoodDiv D)
    (G : ↥(modularFunctionFieldBar (N * q))) (hG : G ∈ riemannRochSpace D)
    (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers) :
    (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) ∧
    (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) ∈ riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)) ∧
    ∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) c ∧
      (arithFrobC q k N • w).HasValue (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) c := by sorry
