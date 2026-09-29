-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentChart_snd_of_isModel
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentChart_snd_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/9dd9b240-29aa-5529-8fc0-90f1c9b22db5
-- title:
--   Component chart for the second copy of X₀(N)
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an integer $N \neq 0$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} \colon A \to k$, modular polynomial data `data` at $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) satisfying the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q) \bmod q$, integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke embeddings at level $(N, q)$, and a place specialisation $P$ of these data. Assume $q \nmid N$, and let $R$ be a prolongation tuple for $P$ which is a model, i.e. satisfies the two divisor laws and the two cusp laws. Give $k(X_0(N)) =$ `modularFunctionFieldC k N` the structure of an algebra over the residue field $\kappa_A$ of $A$ through $R$'s reduction $\kappa_A \to k$. The assertion is that there exist a component chart $C$ for $A$ on $\overline{\mathbb Q}(X_0(Nq)) =$ `modularFunctionFieldBar (N * q)` with residue target $k(X_0(N))$ — so a valuation subring of $\overline{\mathbb Q}(X_0(Nq))$ contracting to $A$, a surjective residue map onto $k(X_0(N))$ with kernel the maximal ideal and compatible with the residue map of $A$, a domain of places, a finite set of nodes, and a place map subject to the pointwise and divisor-transport axioms of `ComponentChart` — together with a map $rc$ from the $k$-places of $k(X_0(N))$ to its $\kappa_A$-places, such that: $rc$ is bijective; $rc\,v$ and $v$ have the same valuation subring and the same order function $\mathrm{ord}$ on $k(X_0(N))$; the integers of $C$ are those of $R.R_2$ and the two residue maps agree on them; the domain of $C$ is the set of places $V$ of $\overline{\mathbb Q}(X_0(Nq))$ that are strict of the second kind for $P$, i.e. $P.\mathrm{reduceFst}\,V = \varphi(P.\mathrm{reduceSnd}\,V)$ and $\varphi(\varphi(P.\mathrm{reduceSnd}\,V)) \neq P.\mathrm{reduceSnd}\,V$, where $\varphi =$ `frobOnPlacesGeomLevel` is the Frobenius operation on places attached to `data` and the Kronecker congruence; $rc\,v$ lies in the nodes of $C$ exactly when $\varphi(\varphi(v)) = v$; and the place map of $C$ is $rc \circ P.\mathrm{reduceSnd}$.
--
--   This constructs, in the language of component charts, the second of the two copies of $X_0(N)_k$ in the special fibre of $X_0(Nq)$ at a prime $q \nmid N$, in the Deligne–Rapoport picture of that fibre as two copies of $X_0(N)$ crossing at the supersingular points: the Gauss prolongation $R.R_2$ supplies the chart's integers and residue map, the places strict of the second kind form its domain, the places fixed by the square of the Frobenius operation are declared nodes, and reduction of places is $P.\mathrm{reduceSnd}$. It feeds the assembly of the two charts with their annuli in `exists_componentCharts_annuli_isAttached_of_crossingPresentation`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentChart_snd_of_isModel.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentChart_snd_of_isModel
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
      C.integers = R.R₂.integers ∧
      (∀ (f : ↥(modularFunctionFieldBar (N * q))) (hC : f ∈ C.integers) (h : f ∈ R.R₂.integers),
        C.residue ⟨f, hC⟩ = R.residue₂ ⟨f, h⟩) ∧
      C.dom = {V | P.IsStrictSnd V} ∧
      (∀ v : Place k ↥(modularFunctionFieldC k N),
        rc v ∈ C.nodes ↔ frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), C.placeMap V = rc (P.reduceSnd V)) := by sorry
