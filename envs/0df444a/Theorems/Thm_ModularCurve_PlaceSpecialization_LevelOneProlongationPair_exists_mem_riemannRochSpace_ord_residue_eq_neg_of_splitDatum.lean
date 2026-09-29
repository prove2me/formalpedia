-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/31359c7a-e21f-52eb-ab67-a89b3c6730a4
-- title:
--   Exact branch orders for a lift keyed on a split datum
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr` (the reduction of $\Phi$ modulo $q$ equals $(C X^q - X)(C X - X^q)$), integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` from level $1$ to level $q$ over $\overline{\mathbb Q}$, a place specialisation $P$ of this data, and a level-one prolongation pair $R$ for $P$, consisting of two regular prolongations $R_1, R_2$ of $A$ to `modularFunctionFieldBar (1 * q)` with the compatibilities recorded in `LevelOneProlongationPair` (residues computed coefficientwise, and $R_2$ obtained from $R_1$ through the Fricke involution). Let $S_0$ be a finite subset of $k$ whose elements are exactly those $j$ such that every elliptic curve over $k$ with invariant $j$ has no nonzero $q$-torsion point, and let $B$ be a finite subset of $k$ such that for each $b \in B$ the place `charLGeomPlaceOfPoint k b` is not fixed by the square of the Frobenius map `frobOnPlacesGeomLevel k 1 data hKr` on places of `modularFunctionFieldC k 1`. Let $E$ be a divisor of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$, let $D_1, D_2$ be divisors of `modularFunctionFieldC k 1` over $k$, let $\mathrm{lam} : k \to k$, and assume `R.SplitDatum S₀ E D₁ D₂ lam`: that is, at places fixed by the square of Frobenius and distinct from $P.\mathrm{redFst}(\bar\infty)$ the values of $D_1$ and of $D_2$ at the Frobenius image are squeezed between the push-forwards under $P.\mathrm{redFst}$ of the negative and of the positive part of $E$ and satisfy $D_1(v) + D_2(\varphi v) = (\mathrm{redFst})_* E(v)$; at the remaining places $D_1$ and $D_2$ are the push-forwards of the strict type-one and type-two parts of $E$; $\deg D_1 + \deg D_2 = \deg E$; $\mathrm{lam}$ is nonvanishing on $S_0$; the values of $D_1$ at $P.\mathrm{redFst}(\bar\infty)$ and of $D_2$ at $P.\mathrm{redSnd}(\bar 0)$ are cut out by the $\infty$-side and $0$-side parts of $E$; and the reductions of any element of the Riemann–Roch space of $E$ integral for both prolongations lie in the Riemann–Roch spaces of $D_1$ and $D_2$ and have prescribed node values at points of $S_0$ governed by $\mathrm{lam}$ (these conditions are summarised here). Assume finally $2g + 1 \le \deg D_1$ and $2g + 1 \le \deg D_2$, where $g$ is `genusFF` of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$. Then there exists $G$ in `modularFunctionFieldBar (1 * q)`, integral for $R_1$ and for $R_2$, with both residues $R_1.\mathrm{residue}(G)$ and $R_2.\mathrm{residue}(G)$ nonzero, lying in the Riemann–Roch space of $E$ (so $v(G) \le \exp(E(v))$ at every place $v$), and such that the level-one reductions $R.\mathrm{residue}_1(G)$, $R.\mathrm{residue}_2(G)$ in `modularFunctionFieldC k 1` realise $-D_1$ and $-D_2$ exactly: $\mathrm{ord}_v(R.\mathrm{residue}_1 G) + D_1(v) = 0$ and $\mathrm{ord}_{\varphi v}(R.\mathrm{residue}_2 G) + D_2(\varphi v) = 0$ for every place $v$ fixed by $\varphi^2$ with $v \ne P.\mathrm{redFst}(\bar\infty)$; $\mathrm{ord}(R.\mathrm{residue}_1 G) + D_1 = 0$ at $P.\mathrm{redFst}(\bar\infty)$; $\mathrm{ord}(R.\mathrm{residue}_2 G) + D_2 = 0$ at $P.\mathrm{redSnd}(\bar 0)$; and both equalities hold at `charLGeomPlaceOfPoint k b` for every $b \in B$.
--
--   This is the moving step in the level-one gluing of $J_0(q)$ at $q$: it produces a function on the modular curve of level $q$ over $\overline{\mathbb Q}$ whose reductions along the two Gauss prolongations have exactly the orders prescribed by the two branch divisors of a split datum, at the Frobenius-stable places, at the two cusp places and at finitely many prescribed non-stable places. It is used by the two results constructing good representatives of admissible classes of the form $\mathrm{smul}$ of a difference of single divisors, according to whether the relevant parameter vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairSplit
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization
open Classical in

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k)
    (B : Finset k)
    (hB : ∀ b ∈ B, frobOnPlacesGeomLevel k 1 data hKr
      (frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k b)) ≠ charLGeomPlaceOfPoint k b)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k) (hsd : R.SplitDatum S₀ E D₁ D₂ lam)
    (hdeg₁ : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) : ℤ) + 1 ≤ D₁.degree)
    (hdeg₂ : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) : ℤ) + 1 ≤ D₂.degree) :
    ∃ (G : modularFunctionFieldBar (1 * q)) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      R.R₁.residue ⟨G, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨G, h₂⟩ ≠ 0 ∧
      G ∈ riemannRochSpace E ∧
      (∀ v : Place k (modularFunctionFieldC k 1),
        frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
        v ≠ P.redFst (cuspInftyBar (1 * q)) →
        v.ord (R.residue₁ ⟨G, h₁⟩) + D₁ v = 0 ∧
        (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨G, h₂⟩) +
          D₂ (frobOnPlacesGeomLevel k 1 data hKr v) = 0) ∧
      ((P.redFst (cuspInftyBar (1 * q))).ord (R.residue₁ ⟨G, h₁⟩) + D₁ (P.redFst (cuspInftyBar (1 * q))) = 0) ∧
      ((P.redSnd (cuspZeroBar (1 * q))).ord (R.residue₂ ⟨G, h₂⟩) + D₂ (P.redSnd (cuspZeroBar (1 * q))) = 0) ∧
      (∀ b ∈ B,
        (charLGeomPlaceOfPoint k b).ord (R.residue₁ ⟨G, h₁⟩) + D₁ (charLGeomPlaceOfPoint k b) = 0 ∧
        (charLGeomPlaceOfPoint k b).ord (R.residue₂ ⟨G, h₂⟩) + D₂ (charLGeomPlaceOfPoint k b) = 0) := by sorry
