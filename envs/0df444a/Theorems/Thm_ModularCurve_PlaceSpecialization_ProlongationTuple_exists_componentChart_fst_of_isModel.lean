-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentChart_fst_of_isModel
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentChart_fst_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/5dfc5dc4-4339-5a89-936d-182f9b3eec30
-- title:
--   First component chart of the special fibre of X₀(Nq)
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}\colon A \to k$, a `ModularPolynomialData` $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) satisfying the Kronecker congruence $\Phi \bmod q = (X^q - Y)(X - Y^q)$, and witnesses $h\alpha$, $h\beta$ that the Hecke maps $\bar\alpha$, $\bar\beta$ at level $(N,q)$ over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a place specialisation of the data $(A, q, N, \mathrm{data}, h_{Kr}, k, \mathrm{red}, h\alpha, h\beta)$, assume $q \nmid N$, and let $R$ be a prolongation tuple for $P$ which is a model (the two divisor laws and the two cusp laws hold). View $k(X_0(N)) =$ `modularFunctionFieldC k N` as an algebra over the residue field $\kappa_A$ of $A$ through $R.\mathrm{redBar}$. The assertion is the existence of a component chart $C$ for $A$ with function field $\overline{\mathbb{Q}}(X_0(Nq)) =$ `modularFunctionFieldBar (N * q)` and residue field $k(X_0(N))$ — that is, a valuation subring $C.\mathrm{integers}$, a surjective residue map onto $k(X_0(N))$ with kernel the maximal ideal and compatible with the residue map of $A$, a set $C.\mathrm{dom}$ of places of $\overline{\mathbb{Q}}(X_0(Nq))$ over $\overline{\mathbb{Q}}$, a finite set $C.\mathrm{nodes}$ of places of $k(X_0(N))$ over $\kappa_A$, and a map $C.\mathrm{placeMap}$ on places satisfying the chart axioms (avoidance of nodes on the domain, pointwise compatibility at rational points of the domain, and the divisor pushforward law) — together with a map $rc$ from the $k$-places of $k(X_0(N))$ to its $\kappa_A$-places such that: $rc$ is bijective and preserves valuation subrings and all orders $\mathrm{ord}$; $C.\mathrm{integers} = R.R_1.\mathrm{integers}$, and the residue maps of $C$ and of $R.R_1$ agree on every common element; $C.\mathrm{dom}$ is exactly the set of places $V$ with $P.\mathrm{IsStrictFst}\,V$, i.e. $\varphi(P.\mathrm{reduceFst}\,V) = P.\mathrm{reduceSnd}\,V$ and $\varphi(\varphi(P.\mathrm{reduceFst}\,V)) \ne P.\mathrm{reduceFst}\,V$, where $\varphi =$ `frobOnPlacesGeomLevel`; $rc\,v$ lies in $C.\mathrm{nodes}$ precisely when $\varphi(\varphi(v)) = v$; and $C.\mathrm{placeMap}\,V = rc(P.\mathrm{reduceFst}\,V)$ for every place $V$.
--
--   This packages the first of the two copies of $X_0(N)_k$ in the special fibre of $X_0(Nq)$ at a prime $q \nmid N$, in the sense of Deligne–Rapoport, as an [`AlgebraicCurve.ComponentChart`](def/AlgebraicCurve_SemistableCharts.html#L15): its ring of integers is the first Gauss prolongation of the tuple, its domain consists of the places strict of the first kind, and its nodes are the places fixed by the square of the Frobenius permutation of places. It is used in the construction of the pair of component charts with attached annuli that presents the crossing of the two components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentChart_fst_of_isModel.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentChart_fst_of_isModel
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (R : ProlongationTuple P) (hR : R.IsModel) :
    letI : Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N) :=
      ((algebraMap k ↥(modularFunctionFieldC k N)).comp R.redBar).toAlgebra
    ∃ (C : ComponentChart A ↥(modularFunctionFieldBar (N * q)) ↥(modularFunctionFieldC k N))
      (rc : Place k ↥(modularFunctionFieldC k N) → Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N)),
      Function.Bijective rc ∧
      (∀ v : Place k ↥(modularFunctionFieldC k N), (rc v).toValuationSubring = v.toValuationSubring) ∧
      (∀ (v : Place k ↥(modularFunctionFieldC k N)) (g : ↥(modularFunctionFieldC k N)), (rc v).ord g = v.ord g) ∧
      C.integers = R.R₁.integers ∧
      (∀ (f : ↥(modularFunctionFieldBar (N * q))) (hC : f ∈ C.integers) (h : f ∈ R.R₁.integers),
        C.residue ⟨f, hC⟩ = R.residue₁ ⟨f, h⟩) ∧
      C.dom = {V | P.IsStrictFst V} ∧
      (∀ v : Place k ↥(modularFunctionFieldC k N),
        rc v ∈ C.nodes ↔ frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), C.placeMap V = rc (P.reduceFst V)) := by sorry
