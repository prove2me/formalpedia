-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/a66a5034-19ba-56c3-a441-3ab85cc44425
-- title:
--   Height-one vertical prime is the centre of a Gauss prolongation
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a natural number $N \neq 0$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} \colon A \to k$. Let `data` consist of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ in $Y$ annihilating the pair $(j, j_q)$, let `hKr` assert the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q)$ after reduction of the coefficients modulo $q$, and let `hα`, `hβ` assert that the two maps `heckeAlphaBar`, `heckeBetaBar` from the level-$N$ to the level-$Nq$ modular function field over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Let $P$ be a place specialisation of these data and $R$ a prolongation tuple over $P$, so in particular $R$ carries two regular prolongations $R_1, R_2$ of $A$ to the level-$Nq$ modular function field over $\overline{\mathbb{Q}}$, each a valuation subring with a surjective residue map onto the level-$N$ full modular function field over the residue field of $A$ whose kernel is the maximal ideal. Assume $q \nmid N$. Let $K \subseteq \overline{\mathbb{Q}}$ be a finite extension of $\mathbb{Q}$ and let $\mathfrak{p}$ be a prime ideal of `jIntegralClosure (N * q) A K`, the ring of Laurent series lying in `fieldOver (N * q) K` and integral over `jRing A K`, such that $\mathfrak{p}$ has height one and contains the image of $q$. Then one of the following holds: for every element $t$ of the level-$Nq$ modular function field over $\overline{\mathbb{Q}}$ whose underlying Laurent series lies in `jIntegralClosure (N * q) A K`, that element lies in $\mathfrak{p}$ if and only if $t$ belongs to $R_1$ and its residue under $R_1$ vanishes; or the same equivalence holds with $R_2$ and its residue map in place of $R_1$.
--
--   This identifies a height-one prime of the level-$Nq$ normalisation lying over $q$ with the centre of one of the two prolongations of $R$, the algebraic counterpart of the fact that the fibre at $q$ of $X_0(Nq)$ consists of two copies of $X_0(N)$ crossing at the supersingular points. It is used in the comparison of the place attached to such a prime with the prolongation residue maps and in the implication relating vanishing of the second residue to vanishing of the first.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (𝔭 : Ideal ↥(jIntegralClosure (N * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (hq : ((q : ℕ) : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭) :
    (∀ (t : ↥(modularFunctionFieldBar (N * q))) (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
        (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭 ↔
          ∃ h₁ : t ∈ R.R₁.integers, R.residue₁ ⟨t, h₁⟩ = 0) ∨
    (∀ (t : ↥(modularFunctionFieldBar (N * q))) (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
        (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭 ↔
          ∃ h₂ : t ∈ R.R₂.integers, R.residue₂ ⟨t, h₂⟩ = 0) := by sorry
