-- Prove2me | Theorems.Thm_ModularCurve_SSLevelDatum_degeneracyMatrix_mulVec_padj_eq_smul_and_eq_vertexHecke_mulVec
-- name    : ModularCurve.SSLevelDatum.degeneracyMatrix_mulVec_padj_eq_smul_and_eq_vertexHecke_mulVec
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/460e3d22-71ec-5100-bda7-0d68fe2f59b3
-- title:
--   Degeneracy degrees s+1 and Tₛ=a_*bᵈagger on supersingular places
-- statement:
--   Fix natural numbers $M,s,q'$ with $M,s$ nonzero, $q'$ prime, $s$ prime ($hs$), $q'\ge 5$, $s\neq q'$, and $q'\nmid M$, $s\nmid M$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $\kappa=$ `IsLocalRing.ResidueField A` has characteristic $q'$, and assume the two sets of supersingular places `ssPlaces q' (M*s) κ` and `ssPlaces q' M κ` — the places of the level-$(M s)$ and level-$M$ function fields `modularFunctionFieldC κ ·` satisfying `IsSupersingularPlace` — are finite with decidable equality. Let $X$ be a datum of type `SSLevelDatum q' κ M s`: it records that `jqNModC κ M` and `jqNModC κ s` lie in `modularFunctionFieldC κ (M*s)`, integrality of the two level maps `levelAlphaC`, `levelBetaC` and of all Hecke legs `heckeAlphaC`, `heckeBetaC`, the fact that restriction along the two level maps carries supersingular places of level $Ms$ to supersingular places of level $M$ (giving the maps $a=$`X.degeneracyData.a` and $b=$`X.degeneracyData.b`), an Atkin–Lehner automorphism of the level-$(Ms)$ field preserving supersingular places, and modular polynomial data `frobData` together with a Kronecker congruence. For $f$ a map of place sets, [`CerednikDrinfeld.degeneracyMatrix f`](def/CerednikDrinfeld_Ribbon.html#L21) is the incidence matrix with $(v,e)$ entry $1$ if $f(e)=v$ and $0$ otherwise, so that `mulVec` by it is pushforward along $f$. The weights are `placeWidth`: on level $M$ the integer $\mathrm{toPNat}'(\mathtt{placeWidth } M\, v)$, on level $Ms$ the component `X.degeneracyData.w e` $=\mathrm{toPNat}'(\mathtt{placeWidth }(Ms)\, e)$, where `placeWidth N w` is $\mathtt{jWidth}(w.\mathtt{evalAt}(\mathtt{jGeomGen}))$ divided by `placeRamificationJ N w`. Let `padj` be a pair (indexed by `Fin 2`) of $\mathbb{Z}$-linear maps from $\mathbb{Z}$-valued functions on the level-$M$ supersingular places to $\mathbb{Z}$-valued functions on the level-$(Ms)$ ones, assumed in $hadj$ to be adjoint to pushforward along $a$ (for $i=0$) and along $b$ (for $i=1$) with respect to these width-weighted pairings. The conclusion is twofold: for each $i\in\{0,1\}$ and each $x$ on the level-$M$ supersingular places, pushing `padj i x` forward along the corresponding map gives $(s+1)\cdot x$; and for each $x$, pushing `padj 1 x` forward along $a$ gives `(X.vertexHecke ⟨s, hs⟩).mulVec x`, where `X.vertexHecke` is the Hecke matrix family `ssHeckeFamilyC q' κ M X.frobData X.kronecker (X.legsIntegral M)` on the level-$M$ supersingular places.
--
--   This is the statement that both degeneracy maps $X_0(Ms)\rightrightarrows X_0(M)$ have degree $s+1$ on supersingular points, and that the Hecke operator $T_s$ at level $M$ is computed as $a_*b^\dagger$ through level $Ms$, in the matrix form used for the character-group (Čerednik–Drinfeld/Ribet) side of level lowering. It is cited by [`ModularCurve.SSLevelDatum.degeneracyMatrix_mulVec_padj_and_edgeHecke_companion_laws`](thm.html#ModularCurve.SSLevelDatum.degeneracyMatrix_mulVec_padj_and_edgeHecke_companion_laws) and [`ModularCurve.SSLevelDatum.exists_heckeRowSums_and_adjointPair_laws`](thm.html#ModularCurve.SSLevelDatum.exists_heckeRowSums_and_adjointPair_laws).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSLevelDatum_degeneracyMatrix_mulVec_padj_eq_smul_and_eq_vertexHecke_mulVec.lean

import Definitions.Def_ModularCurve_SSDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SSLevelDatum.degeneracyMatrix_mulVec_padj_eq_smul_and_eq_vertexHecke_mulVec
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
          (X.vertexHecke ⟨s, hs⟩).mulVec x) := by sorry
