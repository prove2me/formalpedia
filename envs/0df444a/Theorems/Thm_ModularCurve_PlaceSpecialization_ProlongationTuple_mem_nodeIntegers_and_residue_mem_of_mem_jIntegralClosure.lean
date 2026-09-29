-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/45b74e3d-669d-5f6c-b2cb-3d163dbf231c
-- title:
--   Node integrality and regular residues at supersingular places
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an $N\ge 1$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data `data` for $q$ (a monic bivariate integral polynomial $\Phi$ of degree $\psi(q)$ vanishing on $(j,j_q)$) satisfying the Kronecker congruence `hKr`, namely that the reduction of $\Phi$ modulo $q$ equals $(X^q-Y)(X-Y^q)$, together with hypotheses `hα`, `hβ` that the two Hecke base-change ring maps `heckeAlphaBar` and `heckeBetaBar` at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a place specialisation for these data and $R$ a prolongation tuple over $P$, with $k$ algebraically closed and with decidable equality, and assume $q \nmid N$. Let $K$ be a finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$, let $w$ be a place of $k(j, j_N) =$ `modularFunctionFieldC k N` belonging to `ssPlaces q N k`, i.e. satisfying `IsSupersingularPlace q N k`, and let $t$ lie in `modularFunctionFieldBar (N * q)`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $Nq$ inside Laurent series, with underlying Laurent series lying in `jIntegralClosure (N * q) A K`, that is, lying in `fieldOver (N * q) K` and integral over the ring `jRing A K`. Then $t$ lies in `R.nodeIntegers w`: it lies in the integers of both prolongations $R_1$ and $R_2$, and in the valuation subring of every place $V$ of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$ with `P.reduceFst V = w`. Moreover, for any proof that $t$ lies in the integers of $R_1$, its residue `R.residue₁`, viewed in $k(j,j_N)$, lies in the valuation subring of $w$; and for any proof that $t$ lies in the integers of $R_2$, its residue `R.residue₂` lies in the valuation subring of the translate `arithFrobC q k N • w` of $w$ by the semilinear automorphism of $k(j,j_N)$ induced by the $q$-power Frobenius of $k$.
--
--   This is the integrality input for the two-component description of the fibre at $q$ of the level-$Nq$ modular curve: a function whose $q$-expansion is integral over $A\cap K$ adjoined $j$ is regular at each place above a supersingular point $w$, and its restrictions to the two branches are regular at $w$ and at its Frobenius translate respectively. It feeds the subsequent analysis of orders of vanishing of the two residues at the nodes and of the node rings on the normalisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (t : ↥(modularFunctionFieldBar (N * q)))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    t ∈ R.nodeIntegers w ∧
    (∀ h₁ : t ∈ R.R₁.integers, (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring) ∧
    (∀ h₂ : t ∈ R.R₂.integers,
      (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)) ∈ (arithFrobC q k N • w).toValuationSubring) := by sorry
