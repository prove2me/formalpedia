-- Prove2me | Theorems.Thm_ModularCurve_SSLevelDatum_degeneracyMatrix_mulVec_padj_and_edgeHecke_companion_laws
-- name    : ModularCurve.SSLevelDatum.degeneracyMatrix_mulVec_padj_and_edgeHecke_companion_laws
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/3841046e-711b-5f3d-9a0d-6d70f317f864
-- title:
--   Degeneracy adjoints and Hecke companion relations at the prime s
-- statement:
--   Fix natural numbers $M, s, q'$ with $M, s$ nonzero, $q'$ prime, $s$ prime, $q' \ge 5$, $s \ne q'$, and neither $q'$ nor $s$ dividing $M$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $\kappa = \mathrm{ResidueField}(A)$ has characteristic $q'$, and assume the sets $\mathrm{ssPlaces}\,q'\,(Ms)\,\kappa$ and $\mathrm{ssPlaces}\,q'\,M\,\kappa$ of supersingular places of the modular function fields of levels $Ms$ and $M$ over $\kappa$ are finite. Let $X$ be a supersingular level datum `SSLevelDatum q' κ M s`: it records that the level-$M$ and level-$s$ $j$-functions lie in the level-$Ms$ function field, integrality of the resulting degeneracy maps `levelAlphaC`, `levelBetaC` and of all the Hecke maps `heckeAlphaC`, `heckeBetaC`, the fact that restriction along the two degeneracy maps carries supersingular places of level $Ms$ to supersingular places of level $M$ (giving maps $a = X.\mathrm{fst}$ and $b = X.\mathrm{snd}$), an Atkin–Lehner level automorphism preserving the supersingular places, and modular polynomial data satisfying the Kronecker congruence. Write $A_a$ and $A_b$ for the incidence (pushforward) matrices [`CerednikDrinfeld.degeneracyMatrix`](def/CerednikDrinfeld_Ribbon.html#L21) of $a$ and $b$, that is, the $\{0,1\}$-matrices with $(v,e)$-entry $1$ exactly when $a(e) = v$ (resp. $b(e) = v$); write $T_s = X.\mathrm{vertexHecke}\,s$ for the Hecke matrix at $s$ on divisors supported on the level-$M$ supersingular places and $U_s = X.\mathrm{edgeHecke}\,s$ for the Hecke matrix at $s$ on the level-$Ms$ supersingular places. Let $\mathrm{padj}\,0, \mathrm{padj}\,1$ be $\mathbb{Z}$-linear maps from functions on the level-$M$ supersingular places to functions on the level-$Ms$ ones which, by hypothesis, are adjoint to $A_a$ and $A_b$ for the width-weighted pairings: for each $i$ and all $x$, $y$, $\sum_v \mathrm{placeWidth}\,M\,v \cdot (A_{\bullet}y)(v)\,x(v) = \sum_e \mathrm{placeWidth}\,(Ms)\,e \cdot y(e)\,(\mathrm{padj}\,i\,x)(e)$, the widths being taken as positive integers via `Nat.toPNat'`. Then: $A_a(\mathrm{padj}\,0\,x) = (s+1)x$ and $A_b(\mathrm{padj}\,1\,x) = (s+1)x$; $A_a(\mathrm{padj}\,1\,x) = T_s x$ and $A_b(\mathrm{padj}\,0\,x) = T_s x$; and for all $y$ on the level-$Ms$ places, $A_a(U_s y) = T_s(A_a y) - A_b y$ and $A_b(U_s y) = s\,A_a y$.
--
--   These are Ribet's relations for the pair of degeneracy maps between the supersingular divisor groups of levels $Ms$ and $M$ in characteristic $q'$: in matrix form $\delta\delta^\dagger = \begin{pmatrix} s+1 & T_s \\ T_s & s+1\end{pmatrix}$ and $\delta U_s = \begin{pmatrix} T_s & -1 \\ s & 0\end{pmatrix}\delta$ for $\delta = (A_a, A_b)$, expressing that each degeneracy map has degree $s+1$, that $T_s$ is the composite $a_* b^*$, and that $U_s$ acts on the upper level through the standard two-by-two companion matrix. They are used in the rank computations for the Hecke-torsion of the ribbon component group and for the toric monodromy part attached to a supersingular level datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSLevelDatum_degeneracyMatrix_mulVec_padj_and_edgeHecke_companion_laws.lean

import Definitions.Def_ModularCurve_SSDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SSLevelDatum.degeneracyMatrix_mulVec_padj_and_edgeHecke_companion_laws
    (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime] (hs : s.Prime)
    (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q']
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s)
    (padj : Fin 2 → ((↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) →ₗ[ℤ]
      (↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ)))
    (hadj : ∀ (i : Fin 2) (x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ)
        (y : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ),
        (∑ v, (Nat.toPNat' (placeWidth M v.1) : ℤ) *
            (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec y v * x v) =
          ∑ e, (X.degeneracyData.w e : ℤ) * y e * padj i x e) :
    (∀ (i : Fin 2) (x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ),
        (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec (padj i x) =
          (((s : ℕ) : ℤ) + 1) • x) ∧
    (∀ x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ,
        (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.a).mulVec (padj 1 x) =
          (X.vertexHecke ⟨s, hs⟩).mulVec x) ∧
    (∀ x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ,
        (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.b).mulVec (padj 0 x) =
          (X.vertexHecke ⟨s, hs⟩).mulVec x) ∧
    (∀ y : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ,
        (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.a).mulVec ((X.edgeHecke ⟨s, hs⟩).mulVec y) =
          (X.vertexHecke ⟨s, hs⟩).mulVec ((CerednikDrinfeld.degeneracyMatrix X.degeneracyData.a).mulVec y) -
            (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.b).mulVec y) ∧
    (∀ y : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ,
        (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.b).mulVec ((X.edgeHecke ⟨s, hs⟩).mulVec y) =
          ((s : ℕ) : ℤ) • (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.a).mulVec y) := by sorry
