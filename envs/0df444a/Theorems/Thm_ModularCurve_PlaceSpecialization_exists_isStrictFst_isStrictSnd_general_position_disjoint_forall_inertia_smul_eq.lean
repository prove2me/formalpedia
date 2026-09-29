-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
-- name    : ModularCurve.PlaceSpecialization.exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/5d153f9b-007e-515b-b6a6-0672ca2ceacd
-- title:
--   Inertia-fixed strict points in general position over the special fibre
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$, $N\ge 1$, and $k$ an algebraically closed field of characteristic $q$ equipped with a ring homomorphism $red : A \to k$; let `data` be modular-polynomial data for $q$ satisfying the Kronecker congruence `hKr`, and let `hα`, `hβ` assert that the two maps `heckeAlphaBar`, `heckeBetaBar` from the level-$N$ to the level-$Nq$ base-changed modular function field over $\overline{\mathbb{Q}}$ are integral. Given a place specialization $P$ of type `PlaceSpecialization A q N data hKr k red hα hβ`, assume $q \nmid N$. Let $W$ be a non-empty finite set and $B$ a finite set of places of $F :=$ `modularFunctionFieldC k N` $= k(j, j_N)$, and let a divisor $Kc$ and $g_0 \in \mathbb{N}$ satisfy the Riemann–Roch identity $\ell(D) - \ell(Kc - D) = \deg D + 1 - g_0$ for every divisor $D$ of $F/k$. Then there are natural numbers $d_1, d_2$, families $Q_1 : \mathrm{Fin}\,d_1 \to$ places of `modularFunctionFieldBar (N * q)` and $Q_2 : \mathrm{Fin}\,d_2 \to$ such places, finite sets $T_1, T_2$ of places of $F$, and one further place $Q_s$ of the level-$Nq$ field such that: $d_1 + 1 = g_0 + \#W$ and $d_2 = g_0$; each $Q_1 i$ is strict of the first kind, i.e. the geometric Frobenius `frobOnPlacesGeomLevel` carries $P.\mathrm{reduceFst}(Q_1 i)$ to $P.\mathrm{reduceSnd}(Q_1 i)$ while its square does not fix $P.\mathrm{reduceFst}(Q_1 i)$; each $Q_2 j$ is strict of the second kind, i.e. $P.\mathrm{reduceFst}(Q_2 j)$ is the Frobenius image of $P.\mathrm{reduceSnd}(Q_2 j)$ and the square of Frobenius does not fix the latter (here $\mathrm{reduceFst}$, $\mathrm{reduceSnd}$ denote $P.sp$ applied to the restriction of a level-$Nq$ place along `heckeAlphaBar`, respectively `heckeBetaBar`); the maps $i \mapsto P.\mathrm{reduceFst}(Q_1 i)$ and $j \mapsto P.\mathrm{reduceSnd}(Q_2 j)$ are injective, with images exactly $T_1$ and $T_2$; $T_1$ is disjoint from $W$ and from $B$, and $T_2$ is disjoint from $B$; every $v$ in $T_1$ or $T_2$ is an affine geometric place, that is both $j$ and $j_N$ lie in the valuation subring of $v$, and admits a pair $c = (c_1, c_2) \in k \times k$ which is a centre of $v$ (both $\mathrm{ord}_v(j - c_1)$ and $\mathrm{ord}_v(j_N - c_2)$ are positive), is the centre of no other place, and satisfies $\mathrm{ord}_v(j - c_1) = 1$ or $\mathrm{ord}_v(j_N - c_2) = 1$; any $h \in F$ with $\mathrm{ord}_v h \ge 0$ off $T_1$, $\mathrm{ord}_v h \ge -1$ on $T_1$, and residue value $0$ at every $w \in W$ vanishes; any $h \in F$ with $\mathrm{ord}_v h \ge 0$ off $T_2$ and $\mathrm{ord}_v h \ge -1$ on $T_2$ lies in $k$; $Q_s$ is strict of the first kind with $P.\mathrm{reduceFst}(Q_s)$ distinct from every $P.\mathrm{reduceFst}(Q_1 i)$; and every $Q_1 i$ and every $Q_2 j$ is fixed by the action of `arithmeticGalois (modularFunctionFieldFull (N * q)) σ` for every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`.
--
--   This supplies the inertia-stable base divisors used on the two components of the special fibre of $X_0(Nq)$ at $q$: the two families of strict points reduce injectively to sets $T_1$, $T_2$ of smooth points of the plane model, in general position in the Riemann–Roch sense and avoiding prescribed finite sets of places. It is the input to the construction of good divisor classes in the glued-specialization arguments for $J_0(Nq)$, which invoke both the general-position clauses and the inertia invariance.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve
set_option autoImplicit false

theorem ModularCurve.PlaceSpecialization.exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hWne : W.Nonempty)
    (B : Finset (Place k (modularFunctionFieldC k N)))
    (Kc : Divisor k (modularFunctionFieldC k N)) (g₀ : ℕ)
    (hRR : ∀ D : Divisor k (modularFunctionFieldC k N),
      (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g₀) :
    ∃ (d₁ d₂ : ℕ)
      (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      (T₁ T₂ : Finset (Place k (modularFunctionFieldC k N)))
      (Qs : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
      d₁ + 1 = g₀ + W.card ∧ d₂ = g₀ ∧
      (∀ i, P.IsStrictFst (Q₁ i)) ∧ (∀ j, P.IsStrictSnd (Q₂ j)) ∧
      (Function.Injective fun i => P.reduceFst (Q₁ i)) ∧
      (Function.Injective fun j => P.reduceSnd (Q₂ j)) ∧
      (∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v) ∧
      (∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v) ∧
      Disjoint T₁ W ∧ Disjoint T₁ B ∧ Disjoint T₂ B ∧
      (∀ v ∈ T₁, IsAffineGeomPlace k N v) ∧ (∀ v ∈ T₂, IsAffineGeomPlace k N v) ∧
      (∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k N c v ∧
        (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
        (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
          v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1)) ∧
      (∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k N c v ∧
        (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
        (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
          v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1)) ∧
      (∀ h : modularFunctionFieldC k N,
        (∀ v, v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
        (∀ w ∈ W, w.HasValue h 0) → h = 0) ∧
      (∀ h : modularFunctionFieldC k N,
        (∀ v, v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
        ∃ c : k, h = algebraMap k (modularFunctionFieldC k N) c) ∧
      P.IsStrictFst Qs ∧ (∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i)) ∧
      (∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₁ i = Q₁ i) ∧
      (∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₂ j = Q₂ j) := by sorry
