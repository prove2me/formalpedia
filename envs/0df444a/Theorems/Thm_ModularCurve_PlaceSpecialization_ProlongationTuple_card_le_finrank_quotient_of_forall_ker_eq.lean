-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finrank_quotient_of_forall_ker_eq
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.card_le_finrank_quotient_of_forall_ker_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/22cebaeb-619f-5f0e-bae2-2f1ecdf07e28
-- title:
--   Places on one branch bounded by that branch's W-rank
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, $N\neq 0$, a field $k$ of characteristic $q$, a ring homomorphism $red\colon A\to k$, modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two Hecke maps $\bar\alpha,\bar\beta$, and a place specialisation $P$ with a prolongation tuple $R$; let $k$ be perfect, $K$ a finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$, $w$ a place of $modularFunctionFieldC\ k\ N$, and write $B=R.nodeIntegersOver\ K\ w$ (the functions in $\overline{\mathbb Q}$-modular function field of level $Nq$ integral for $R_1$, for $R_2$, and at every place above $w$, with coefficients in the field over $K$) and $\mathcal O=A\cap K$. Assume: node coordinates $c=(x,y)$ over $K$ at $w$; $\varpi\in\mathcal O$ nonzero; $B$ local and noetherian with $\mathfrak m_B=(\varpi,x,y)$ (constants via $R.nodeConst$); every $g\in B$ differs from some constant by a non-unit; the value integrality law at $w$ (every place $V$ with $P.reduceFst\ V=w$ takes values in $A$ on node integers); $w$ supersingular; $W$ a complete discrete valuation domain with irreducible $\pi$, $E\ge 1$, and a ring isomorphism $\iota$ from the $\mathfrak m_B$-adic completion of $B$ onto $W[[U,V]]/(UV-\pi^E)$ carrying $\varpi$ to the constant $\pi$ and $x$ to $U$ times a unit; $\mathcal O$ a discrete valuation ring with $\mathfrak m_{\mathcal O}=(\varpi)$, and an isomorphism $\tau$ from its completion onto $W$ matching constants through $\iota$ and sending $\varpi$ to $\pi$. Let $\mathfrak q\subseteq B$ be an ideal whose image ideal in the model has $W$-module-finite quotient, $Q$ a prime of the model, and $S$ a finite set of places $V$ of the level-$Nq$ function field over $\overline{\mathbb Q}$ such that each $V\in S$ satisfies $P.reduceFst\ V=w$, has $\{g\in B: V.evalAt\ g=0\}=\mathfrak q$, and admits a ring homomorphism $\psi$ from the completion of $B$ to the valuation integers of the completion of $A.valuation$ agreeing with evaluation at $V$ on $B$ and with $\ker(\psi\circ\iota^{-1})=Q$; assume further that places of $S$ agreeing on all of $B$ coincide. Then $\#S\le \operatorname{finrank}_W$ of the model modulo $Q$, as an inequality in $\mathbb N_\infty$.
--
--   This is the single-branch form of the dictionary between places of the modular function field of level $Nq$ lying over a supersingular node and the crossing model $W[[U,V]]/(UV-\pi^E)$: places whose completed evaluation has a prescribed kernel prime $Q$ are bounded in number by the $W$-rank of the corresponding branch quotient. It feeds the two counting results that express products of values at such places as norms of quotients of the crossing model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finrank_quotient_of_forall_ker_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000

universe u

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open ModularCurve.UVCrossingModel Valued in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.card_le_finrank_quotient_of_forall_ker_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : ϖ ≠ 0)
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ})
    (hτ : ∃ τ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K))
        ↥(NodeLocalized.coeffSubring A K) ≃+* W,
      (∀ o : ↥(NodeLocalized.coeffSubring A K),
        ι (algebraMap _ _ (R.nodeConst K w o)) = const (π ^ E) (τ (algebraMap _ _ o))) ∧
      τ (algebraMap _ _ ϖ) = π)
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w))
    (hJfin : Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮))
    (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hS : ∀ V ∈ S, P.reduceFst V = w ∧
      (∀ g : ↥(R.nodeIntegersOver K w), g ∈ 𝔮 ↔ V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) = 0) ∧
      ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) →+*
          𝒪[(A.valuation).Completion],
        (∀ g : ↥(R.nodeIntegersOver K w),
          ((ψ (algebraMap ↥(R.nodeIntegersOver K w) _ g) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
            ((V.evalAt (g : ↥(modularFunctionFieldBar (N * q))) : AlgebraicClosure ℚ) : (A.valuation).Completion)) ∧
        Q.asIdeal = RingHom.ker (ψ.comp ι.symm.toRingHom))
    (hsep : ∀ V ∈ S, ∀ V' ∈ S,
      (∀ g : ↥(R.nodeIntegersOver K w), V.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))
        = V'.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))) → V = V') :
    (S.card : ℕ∞) ≤ (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) := by sorry
