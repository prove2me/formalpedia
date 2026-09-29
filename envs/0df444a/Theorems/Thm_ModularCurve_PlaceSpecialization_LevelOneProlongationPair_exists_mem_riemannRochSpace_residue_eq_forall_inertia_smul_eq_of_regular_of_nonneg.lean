-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_riemannRochSpace_residue_eq_forall_inertia_smul_eq_of_regular_of_nonneg
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_residue_eq_forall_inertia_smul_eq_of_regular_of_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/b30f290f-c850-54b2-82bb-47ccdc4355a2
-- title:
--   Inertia-equivariant lift of a node-compatible residue pair
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k=$ `ResidueField A` has characteristic $q$, let `data` be a modular polynomial datum for $q$ satisfying the Kronecker congruence `hKr`, and let `hα`, `hβ` assert integrality of the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the level-$1$ modular function field into the level-$1\cdot q$ one over $\overline{\mathbb Q}$. Fix a place specialisation $P$ from places of $\overline{\mathbb Q}(X_0(1\cdot q))$ to places of the level-one function field over $k$, attached to the residue map of $A$, and a level-one prolongation pair $R$ for $P$: a coefficientwise reduction $\iota$ together with two regular prolongations $R_1,R_2$ of $A$ to $\overline{\mathbb Q}(X_0(1\cdot q))$ whose residue field is the full level-one modular function field over $k$, related by the Fricke involution. Assume the four model laws `hR` (the two divisor laws and the two cusp laws), the order law `hO` at places fixed by the square of the geometric Frobenius, and the node value law `hval`, summarised here; let $S_0$ be a finite set whose elements are exactly the supersingular $j$-invariants in $k$, i.e. those $j$ for which every elliptic curve over $k$ with invariant $j$ has no nonzero $q$-torsion point, and assume the regularity law `hNR` for $S_0$. Let $D$ be a divisor with $0\le D(W)$ for all $W$, good for $P$ (every point of its support is of strict type one or strict type two for the Frobenius on level-one places), and of degree satisfying $2g\le \deg D+1$, where $g$ is the genus of $\overline{\mathbb Q}(X_0(1\cdot q))$. Let $g_1,g_2$ be elements of the full level-one modular function field over $k$ such that $\iota g_1$ lies in the Riemann–Roch space of the `redFst`-pushforward of the strict type-one part of $D$, $\iota g_2$ lies in that of the `redSnd`-pushforward of the strict type-two part, and for every $a\in S_0$ there is $c\in k$ such that the two places of the node pair attached to $a$, namely those of $a$ and of $a^q$, take the value $c$ at $\iota g_1$ and at $\iota g_2$ respectively. Let $V_0$ be any place of $\overline{\mathbb Q}(X_0(1\cdot q))$, and suppose every point of the support of $D$ is fixed by the `arithmeticGalois` action of each element of the inertia subgroup `A.inertiaSubgroupIn ℚ`. Then there exists $G$ in $\overline{\mathbb Q}(X_0(1\cdot q))$, integral for both $R_1$ and $R_2$, lying in the Riemann–Roch space of $D$, with $R_1$-residue $g_1$ and $R_2$-residue $g_2$, and fixed by every $\sigma$ in `A.inertiaSubgroupIn ℚ` whose `arithmeticGalois` action fixes $V_0$.
--
--   This is the equivariant form of the level-one moving lemma: a prescribed node-compatible pair of residues on the two components of the reduction is lifted to a function in $L(D)$ that is moreover invariant under the stabiliser of a chosen place inside the inertia group of $A$ over $\mathbb Q$. It is used to produce a function with a simple zero at a single place whose two reductions avoid prescribed places, with the invariance needed for the descent step in the analysis of the fibre at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_riemannRochSpace_residue_eq_forall_inertia_smul_eq_of_regular_of_nonneg.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_residue_eq_forall_inertia_smul_eq_of_regular_of_nonneg
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}
    (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hval : LevelOneProlongationPair.NodeValueLaw q (IsLocalRing.residue A))
    (S₀ : Finset (ResidueField A)) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q (ResidueField A)) (hNR : R.RegularityLaw S₀)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hD : ∀ W, 0 ≤ D W) (hgood : P.IsGoodDivisor D)
    (hdeg : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) : ℤ) ≤ D.degree + 1)
    (g₁ g₂ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1)
    (hg₁ : (R.ι g₁ : modularFunctionFieldC (ResidueField A) 1) ∈
      riemannRochSpace (Finsupp.mapDomain P.redFst (P.fstPart D)))
    (hg₂ : (R.ι g₂ : modularFunctionFieldC (ResidueField A) 1) ∈
      riemannRochSpace (Finsupp.mapDomain P.redSnd (P.sndPart D)))
    (hnode : ∀ a ∈ S₀, ∃ c : ResidueField A,
      (frobNodePair q a).1.HasValue (R.ι g₁ : modularFunctionFieldC (ResidueField A) 1) c ∧
      (frobNodePair q a).2.HasValue (R.ι g₂ : modularFunctionFieldC (ResidueField A) 1) c)
    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hDfix : ∀ W ∈ D.support, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • W = W) :
    ∃ (G : modularFunctionFieldBar (1 * q)) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      G ∈ riemannRochSpace D ∧ R.R₁.residue ⟨G, h₁⟩ = g₁ ∧ R.R₂.residue ⟨G, h₂⟩ = g₂ ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ,
          arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V₀ = V₀ →
            arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • G = G := by sorry
