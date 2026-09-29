-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/207587af-fecb-5709-ac76-29257dd03227
-- title:
--   Inertia-fixed lift of a residue pair to L(D)
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a natural number $N \neq 0$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data for $q$ satisfying the Kronecker congruence $\Phi \bmod q = (X'^q - X)(X' - X^q)$, integrality hypotheses for the two degeneracy maps $\overline{\alpha}, \overline{\beta}$ from level $N$ to level $Nq$, and a place specialisation $P$ in this data. Assume $q \nmid N$, and let $W$ be a finset of places of $\mathrm{modularFunctionFieldC}\ k\ N$ whose elements are exactly the supersingular places (rational, affine geometric, with supersingular $j$-value). Let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and the node-value law at $W$, and the order law at places fixed by the square of the geometric Frobenius on places. Let $S$ be a set of $\mathbb{Q}$-automorphisms of $\overline{\mathbb{Q}}$ all lying in the inertia subgroup of $A$ over $\mathbb{Q}$. Let $D$ be an effective divisor on the level-$Nq$ geometric function field $\mathrm{modularFunctionFieldBar}(Nq)$ which is good for $P$ (each place of its support is strict for the first or for the second leg), and suppose every place of the support of $D$ is fixed by the semilinear coefficientwise action of $\mathrm{arithmeticGalois}\ \sigma$ for each $\sigma \in S$. Writing $g_0$ for $\mathrm{genusFF}\ k\ (\mathrm{modularFunctionFieldC}\ k\ N)$, assume the push-forward along $P.\mathrm{reduceFst}$ of the strict-first part of $D$ has degree at least $2g_0 - 1 + |W|$, and the push-forward along $P.\mathrm{reduceSnd}$ of the strict-second part has degree at least $2g_0 - 1$. Finally let $g_1, g_2$ be elements of $\mathrm{modularFunctionFieldFullC}(\mathrm{ResidueField}\ A)\ N$ whose images $R.\iota g_1$, $R.\iota g_2$ lie in the Riemann–Roch spaces of those two push-forward divisors respectively, and such that for every node pair $s = (w, \mathrm{arithFrobC}\ q\ k\ N \cdot w)$ with $w \in W$ there is a common value $c \in k$ taken by $R.\iota g_1$ at $s_1$ and by $R.\iota g_2$ at $s_2$. Then there exists $G$ in $\mathrm{modularFunctionFieldBar}(Nq)$ lying in the integers of both regular prolongations $R.R_1$ and $R.R_2$, with $G \in \mathrm{riemannRochSpace}\ D$, with residues $R.R_1$-residue of $G$ equal to $g_1$ and $R.R_2$-residue of $G$ equal to $g_2$, and with $\mathrm{arithmeticGalois}\ \sigma \cdot G = G$ for every $\sigma \in S$.
--
--   This is the lifting step that realises a prescribed pair of sections on the two components of the special fibre of the model of $X_0(Nq)$ at $q$ by a single function of the level-$Nq$ geometric function field in $L(D)$, and strengthens the corresponding statement without Galois equivariance by producing a section fixed by the given inertia elements. It feeds the construction of local equations and of divisors with prescribed strict behaviour at the two legs, in the geometric part of Ribet's level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open ModularCurve
open AlgebraicCurve

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hS : ∀ σ ∈ S, σ ∈ A.inertiaSubgroupIn ℚ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : 0 ≤ D) (hgood : P.IsGoodDiv D)
    (hDfix : ∀ V ∈ D.support, ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V)
    (hdeg₁ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card ≤
      (Finsupp.mapDomain P.reduceFst (P.fstDiv D)).degree)
    (hdeg₂ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤
      (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)).degree)
    (g₁ g₂ : ↥(modularFunctionFieldFullC (ResidueField A) N))
    (hg₁ : (R.ι g₁ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv D)))
    (hg₂ : (R.ι g₂ : ↥(modularFunctionFieldC k N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)))
    (hnode : ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W, ∃ c : k,
      s.1.HasValue (R.ι g₁ : ↥(modularFunctionFieldC k N)) c ∧
      s.2.HasValue (R.ι g₂ : ↥(modularFunctionFieldC k N)) c) :
    ∃ (G : ↥(modularFunctionFieldBar (N * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      G ∈ riemannRochSpace D ∧ R.R₁.residue ⟨G, h₁⟩ = g₁ ∧ R.R₂.residue ⟨G, h₂⟩ = g₂ ∧
        ∀ σ ∈ S, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • G = G := by sorry
