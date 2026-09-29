-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/b8698e78-38a5-54cf-9bcc-f22196d14de9
-- title:
--   Strict two-sided representative of a good degree-zero class
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbf Q}$, a level $N\neq 0$, an algebraically closed field $k$ of characteristic $q$, a ring map $\mathrm{red}:A\to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality of the two level-raising maps $\bar\alpha,\bar\beta$ from level $N$ to level $Nq$, and a place specialization $P$ for these data; assume $q\nmid N$. Let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and the node-value law at a finset $W$ consisting exactly of the supersingular places of `modularFunctionFieldC k N`, and `OrderLawFixed`. Let $Q_1:\mathrm{Fin}\,d_1\to$ places of `modularFunctionFieldBar (N*q)` with each $Q_1 i$ strict of the first kind ($\mathrm{Frob}(\mathrm{red}_1 Q_1 i)=\mathrm{red}_2 Q_1 i$ and $\mathrm{Frob}^2(\mathrm{red}_1 Q_1 i)\neq \mathrm{red}_1 Q_1 i$) and $Q_2$ with each $Q_2 j$ strict of the second kind, the maps $i\mapsto\mathrm{red}_1 Q_1 i$ and $j\mapsto\mathrm{red}_2 Q_2 j$ injective with images the finsets $T_1$, $T_2$; assume $T_1$ disjoint from $W$, all places of $T_1\cup T_2$ affine geometric (both $j$ and $j_N$ in the valuation subring), that every $h$ in the level-$N$ function field with $\mathrm{ord}\ge 0$ off $T_1$, $\mathrm{ord}\ge -1$ on $T_1$ and value $0$ at each $w\in W$ vanishes, that every $h$ with $\mathrm{ord}\ge 0$ off $T_2$ and $\ge -1$ on $T_2$ is a constant, and $d_1+d_2=\mathrm{genusFF}$ of `modularFunctionFieldBar (N*q)`. Let $D$ be a degree-zero divisor there, good (every place of its support strict of the first or second kind), whose glue datum $(\mathrm{red}_{1*}(D|_{\text{1st}}),\mathrm{red}_{2*}(D|_{\text{2nd}}),0)$ along the node pairs $(w,\mathrm{arithFrob}\cdot w)$, $w\in W$, is admissible and has zero class in the glued degree-zero class group. Then there are places $Q_1'i$ strict of the first kind with $\mathrm{red}_1 Q_1'i=\mathrm{red}_1 Q_1 i$ and $Q_2'j$ strict of the second kind with $\mathrm{red}_2 Q_2'j=\mathrm{red}_2 Q_2 j$ such that $\sum_i Q_1'i+\sum_j Q_2'j-\big(\sum_i Q_1 i+\sum_j Q_2 j\big)$ has degree zero and its class in $\mathrm{Pic}^0$ equals the class of $D$.
--
--   This is the divisor-level form of the canonical-representative step for the two-copy special fibre of $X_0(Nq)$ at $q$: a good degree-zero class whose glued specialization datum is trivial is moved, inside its class, to a difference of effective divisors supported at places strict of the first and second kind with prescribed reductions on each side. It is used by [`ModularCurve.PlaceSpecialization.exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel) and by [`ModularCurve.PlaceSpecialization.pic0Mk_eq_zero_of_isGoodDiv_of_mk_glueData_eq_zero_of_nsmul_eq_zero_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.pic0Mk_eq_zero_of_isGoodDiv_of_mk_glueData_eq_zero_of_nsmul_eq_zero_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open ModularCurve
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
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
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W)
        (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W))
    (hmk : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W)
        ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k N) W)
          (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), hadm⟩ = 0) :
    ∃ (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      (∀ i, P.IsStrictFst (Q₁' i)) ∧ (∀ j, P.IsStrictSnd (Q₂' j)) ∧
      (∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i)) ∧
      (∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j)) ∧
      ∃ hdeg0 : (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
          - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
          Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈
            Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
        Pic0.mk ⟨_, hdeg0⟩ = Pic0.mk D := by sorry
