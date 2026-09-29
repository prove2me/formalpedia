-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/67cc2e52-e014-5c90-83a8-73046611043a
-- title:
--   Strict two-sided representatives of good classes killed by sp
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbf{Q}}$, a level $N\ge 1$ with $q\nmid N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A\to k$, modular polynomial data for $q$ satisfying the Kronecker congruence $\Phi \equiv (X^q_{\text{coeff}} - X)(X_{\text{coeff}} - X^q)$ mod $q$, integrality of the two degeneracy embeddings $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ of $\overline{\mathbf{Q}}$-function fields from level $N$ to level $Nq$, and a place specialisation $P$ for these data. Let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), $W$ the finite set consisting exactly of the supersingular places of the level-$N$ geometric function field over $k$ (rational, affine, with supersingular $j$-value), and assume $R$ satisfies `RegularityLaw W`. Let $sp$ be an additive map from the $A$-inertia invariants of $J_0(Nq)=\mathrm{Pic}^0$ of the level-$Nq$ field over $\overline{\mathbf{Q}}$ to the glued $\mathrm{Pic}^0$ attached to the node pairs $\{(w,\ \mathrm{arithFrob}_q\, w)\}_{w\in W}$, which is a glued specialisation for $P$. Let $Q_1:\mathrm{Fin}\,d_1\to$ places of the level-$Nq$ field be strict of the first kind (Frobenius carries $\mathrm{reduceFst}$ to $\mathrm{reduceSnd}$ and $\mathrm{reduceFst}$ is not fixed by Frobenius squared), $Q_2:\mathrm{Fin}\,d_2\to$ places strict of the second kind, with $i\mapsto \mathrm{reduceFst}(Q_1 i)$ and $j\mapsto\mathrm{reduceSnd}(Q_2 j)$ injective, images $T_1$, $T_2$ consisting of affine places, $T_1$ disjoint from $W$, and the general-position conditions: every $h$ regular off $T_1$, with poles of order at most one on $T_1$, taking value $0$ at every $w\in W$, vanishes; every $h$ regular off $T_2$ with poles of order at most one on $T_2$ is a constant from $k$. Assume $d_1+d_2$ equals the genus of the level-$Nq$ field over $\overline{\mathbf{Q}}$. Then for every inertia-invariant $x$ whose class in $J_0(Nq)$ is good for these node pairs (represented by a degree-zero divisor all of whose support is strict of the first or second kind and whose glue datum is admissible) and with $sp\,x=0$, there are $Q_1':\mathrm{Fin}\,d_1\to$ places strict of the first kind and $Q_2':\mathrm{Fin}\,d_2\to$ places strict of the second kind with $\mathrm{reduceFst}(Q_1' i)=\mathrm{reduceFst}(Q_1 i)$ and $\mathrm{reduceSnd}(Q_2' j)=\mathrm{reduceSnd}(Q_2 j)$ for all $i,j$, such that the divisor $\sum_i Q_1' i+\sum_j Q_2' j-\big(\sum_i Q_1 i+\sum_j Q_2 j\big)$ has degree zero and represents $x$ in $\mathrm{Pic}^0$.
--
--   This is the canonical-representative step in the elementary proof that reduction is injective on the relevant part of $J_0(Nq)$: a class killed by the glued specialisation is rewritten, relative to a fixed two-sided base divisor in general position, as an effective divisor with prescribed reductions on the two copies of the level-$N$ special fibre. It is used by the two subsequent results deducing from $sp\,x=0$ that $x$ itself vanishes, respectively that a suitable multiple of $x$ is attained.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hRL : R.RegularityLaw W)
    {sp : ↥(inertiaInvariants A (N * q)) →+
      GluedPic0 k ↥(modularFunctionFieldC k N) (nodePairsOfPlaces (arithFrobC q k N) W)}
    (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q k N) W) sp)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k N))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k N v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k N v)
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k N) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (x : ↥(inertiaInvariants A (N * q)))
    (hgood : P.IsGoodClass (nodePairsOfPlaces (arithFrobC q k N) W) (x : JZero (N * q)))
    (hx : sp x = 0) :
    ∃ (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      (∀ i, P.IsStrictFst (Q₁' i)) ∧ (∀ j, P.IsStrictSnd (Q₂' j)) ∧
      (∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i)) ∧
      (∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j)) ∧
      ∃ hdeg0 : (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
          - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
          Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈
            Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
        Pic0.mk ⟨_, hdeg0⟩ = (x : JZero (N * q)) := by sorry
