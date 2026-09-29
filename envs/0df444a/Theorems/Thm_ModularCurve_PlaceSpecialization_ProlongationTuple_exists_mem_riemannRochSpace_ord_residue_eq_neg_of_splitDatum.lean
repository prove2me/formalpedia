-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/8cde8c5f-aa83-5b5a-a2f9-8d35a1a6f85b
-- title:
--   Riemann–Roch functions with prescribed residue orders on both prolongations
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr` (the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$), integrality hypotheses `hα`, `hβ` for the two degeneracy embeddings of the level-$N$ function field into the level-$Nq$ one over $\overline{\mathbb Q}$, and a place specialisation $P$ from the places of `modularFunctionFieldBar N` to the places of `modularFunctionFieldC k N`. Assume $q \nmid N$, and let $R$ be a prolongation tuple for $P$, consisting of two regular prolongations `R.R₁`, `R.R₂` of $A$ to `modularFunctionFieldBar (N * q)` with residue fields in the level-$N$ function field over the residue field of $A$, together with the comparison data of the structure. Let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places `ssPlaces q N k` (rational, affine, with $j$-value in `ssJSet`), let $\pi$ assign an element of the function field to each place, let $B$ be a further finite set of places, let $E$ be a divisor on `modularFunctionFieldBar (N * q)` over $\overline{\mathbb Q}$, let $D_1, D_2$ be divisors on `modularFunctionFieldC k N` over $k$, and let $\lambda$ be a $k$-valued function on places. Assume `R.SplitDatum W π E D₁ D₂ lam`, which asserts (summarised here) that $\pi$ is a uniformiser at each $w \in W$, that $\lambda$ is non-zero on $W$, that $D_1$ and $D_2$ are squeezed between, and add up to, the push-forwards along `P.reduceFst` and `P.reduceSnd` of $E$ and of its positive and negative parts, with $\deg D_1 + \deg D_2 = \deg E$, with prescribed values at the two cusp families, and a compatibility condition on elements of `riemannRochSpace E` integral for both prolongations. Assume finally $\deg D_1 \ge 2g + 1$ and $\deg D_2 \ge 2g + 1$, where $g$ is `genusFF` of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb Q}$. Then there is $G$ in `modularFunctionFieldBar (N * q)` lying in the integers of both `R.R₁` and `R.R₂`, with both residues non-zero, lying in `riemannRochSpace E` (that is, $\mathrm{ord}_V(G) \ge -E(V)$ for all $V$), such that: for every place $v$ of `modularFunctionFieldC k N` fixed by the square of `frobOnPlacesGeomLevel k N data hKr` and affine (both `jGeomGen` and `jNGeomGen` lie in its valuation ring), $\mathrm{ord}_v$ of the first residue of $G$ equals $-D_1(v)$ and $\mathrm{ord}$ at the Frobenius image of $v$ of the second residue of $G$ equals $-D_2$ of that image; for every place $c$ of the level-$Nq$ field on the infinity side of $P$, $\mathrm{ord}$ at `P.reduceFst c` of the first residue equals $-D_1(\mathrm{P.reduceFst}\, c)$; for every place $c$ on the zero side, $\mathrm{ord}$ at `P.reduceSnd c` of the second residue equals $-D_2(\mathrm{P.reduceSnd}\, c)$; and for every $b \in B$ both residues have orders $-D_1(b)$ and $-D_2(b)$ at $b$.
--
--   This is the level-$N$ form of the Riemann–Roch construction used to manufacture a function on the curve of level $Nq$ whose reductions along the two prolongations have exactly the divisors $-D_1$ and $-D_2$ prescribed by a split datum at the fixed affine places, at the places coming from the two cusp families, and at a further prescribed finite set of places. It feeds the construction of good representatives of divisor classes in [`ModularCurve.PlaceSpecialization.exists_goodRep_admissible_smul_single_sub_self_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_goodRep_admissible_smul_single_sub_self_of_isModel), on the way to the description of the special fibre of $X_0(Nq)$ at $q$ as two copies of $X_0(N)$ crossing at the supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false
open IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    (R : ProlongationTuple P)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (π : Place k (modularFunctionFieldC k N) → modularFunctionFieldC k N)
    (B : Finset (Place k (modularFunctionFieldC k N)))
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (D₁ D₂ : Divisor k (modularFunctionFieldC k N)) (lam : Place k (modularFunctionFieldC k N) → k)
    (hsd : R.SplitDatum W π E D₁ D₂ lam)
    (hdeg₁ : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) : ℤ) + 1 ≤ D₁.degree)
    (hdeg₂ : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) : ℤ) + 1 ≤ D₂.degree) :
    ∃ (G : modularFunctionFieldBar (N * q)) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      R.R₁.residue ⟨G, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨G, h₂⟩ ≠ 0 ∧ G ∈ riemannRochSpace E ∧
      (∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        IsAffineGeomPlace k N v →
          v.ord (R.residue₁ ⟨G, h₁⟩ : modularFunctionFieldC k N) + D₁ v = 0 ∧
          (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨G, h₂⟩ : modularFunctionFieldC k N)
            + D₂ (frobOnPlacesGeomLevel k N data hKr v) = 0) ∧
      (∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), IsInftySide P c →
        (P.reduceFst c).ord (R.residue₁ ⟨G, h₁⟩ : modularFunctionFieldC k N) + D₁ (P.reduceFst c) = 0) ∧
      (∀ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), IsZeroSide P c →
        (P.reduceSnd c).ord (R.residue₂ ⟨G, h₂⟩ : modularFunctionFieldC k N) + D₂ (P.reduceSnd c) = 0) ∧
      (∀ b ∈ B,
        b.ord (R.residue₁ ⟨G, h₁⟩ : modularFunctionFieldC k N) + D₁ b = 0 ∧
        b.ord (R.residue₂ ⟨G, h₂⟩ : modularFunctionFieldC k N) + D₂ b = 0) := by sorry
