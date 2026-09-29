-- Prove2me | Theorems.Thm_ModularCurve_pow_finrank_quotient_old_add_ribbon_le_natCard_twoPlaceTorsionDatum_fst_W
-- name    : ModularCurve.pow_finrank_quotient_old_add_ribbon_le_natCard_twoPlaceTorsionDatum_fst_W
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/a7a76881-3937-5dde-b41b-0657570e4e8d
-- title:
--   Old and ribbon terms bounded by the first-place torsion subgroup
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $N, q, q'$ be natural numbers with $q$ and $q'$ prime, $q' \neq q$, and $q \nmid N$, $q' \nmid N$ (together with the evident non-vanishing assumptions on $N$, $q$, $q'$ and $Nq'$). Let $\mathfrak m$ be a maximal ideal of the abstract Hecke algebra `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$ with $p \in \mathfrak m$, such that $\mathfrak m$ is not eventually Eisenstein (there is no finite set $S$ of primes with $T_\ell - (\ell + 1) \in \mathfrak m$ for all $\ell \notin S$), and such that $T_{q'}^2 - 1 \in \mathfrak m$; assume moreover $p \nmid q' - 1$ and $p \mid q - 1$ in $\mathbb{Z}$. Let $A_1$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q'$ a non-unit of $A_1$, and $A_2$ a valuation subring whose residue field $k_2$ has characteristic $q$ and for which the sets $\mathrm{ssPlaces}\,q\,(Nq')\,k_2$ and $\mathrm{ssPlaces}\,q\,N\,k_2$ of supersingular places of the level-$Nq'$ and level-$N$ modular function fields over $k_2$ are finite. Let $X_2$ be a supersingular level datum for $q$, $k_2$, levels $N$ and $q'$, satisfying its Hecke laws (commutation of the edge and vertex Hecke matrices, equivariance of the two degeneracy boundary maps away from $q'$, and stability of their common kernel). Let $Y_{o,2}$ be a `HeckeAlg`-module, finite over $\mathbb{Z}$, together with an additive isomorphism $e_{Y_2}$ onto the ribbon kernel $\ker(\alpha_*) \cap \ker(\beta_*)$ of the degeneracy data of $X_2$, carrying the action of each $T_\ell$ to `heckeKernelMap` of the Hecke data of $X_2$ at $\ell$; and let $X_{o,2}$ be a `HeckeAlg`-module, finite over $\mathbb{Z}$, with an additive isomorphism $e_{X_2}$ onto two copies of the degree-zero lattice on $\mathrm{ssPlaces}\,q\,N\,k_2$, such that for each prime $\ell \neq q'$ the operator $T_\ell$ acts diagonally by the vertex Hecke matrix $(X_2.\mathrm{vertexHecke}\,\ell)$, while $T_{q'}$ sends $(x_1, x_2)$ to $\bigl((X_2.\mathrm{vertexHecke}\,q')x_1 - x_2,\; q' x_1\bigr)$. Finally let $E_2, V_2$ be finite types with degeneracy data $D_2$ and Hecke data $H_2$, and let $\mathcal{J}$ be a two-place $p$-torsion datum for the degeneracy and Hecke data of $X_2$, for $D_2$, $H_2$, and for the places $A_1$, $A_2$, whose first-place datum $\mathcal{J}.\mathrm{fst}$ (the $p$-torsion module with its Hecke action, Galois action, toric subgroup, toric identification and specialisation map at $A_1$) satisfies the local laws `LocalLaws` at $q'$. Writing $k = \mathrm{HeckeAlg}/\mathfrak m$, the conclusion is
--   $$|k|^{\;\dim_k (X_{o,2}/\mathfrak m X_{o,2}) \; + \; \dim_k (Y_{o,2}/\mathfrak m Y_{o,2})} \le \#\,\mathcal{J}.\mathrm{fst}.W\,\mathfrak m,$$
--   where $\mathcal{J}.\mathrm{fst}.W\,\mathfrak m$ is the subgroup of the torsion module of $\mathcal{J}$ attached to $\mathfrak m$, all cardinalities being taken as `Nat.card`.
--
--   This is the auxiliary-prime half of Ribet's exchange argument carried out on the Shimura curve of discriminant $qq'$: at a place over $q'$ the reduction is purely toric (Čerednik–Drinfeld), and the character-group (ribbon) contribution together with the $q'$-old contribution are shown jointly to fit inside the $\mathfrak m$-part of the torsion datum. It feeds the two comparisons [`ModularCurve.finrank_quotient_old_add_ribbon_le_finrank_quotient_ribbon_of_twoPlaceTorsionDatum_of_le_invariants`](thm.html#ModularCurve.finrank_quotient_old_add_ribbon_le_finrank_quotient_ribbon_of_twoPlaceTorsionDatum_of_le_invariants) and its variant with an extra divisibility hypothesis, which are the level-lowering inequalities at the auxiliary prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pow_finrank_quotient_old_add_ribbon_le_natCard_twoPlaceTorsionDatum_fst_W.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_MazurPrincipleCore
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.pow_finrank_quotient_old_add_ribbon_le_natCard_twoPlaceTorsionDatum_fst_W
    (p : ℕ) [Fact p.Prime] {N q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hqN : ¬ q ∣ N) (hqq' : q' ≠ q)
    (hp2 : p ≠ 2) (hq'N : ¬ q' ∣ N) [NeZero (N * q')] [NeZero q]
    [NeZero N] [NeZero q'] [Fact q.Prime] [Fact q'.Prime]
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : (p : HeckeAlg) ∈ 𝔪) (heis : ¬ IsEventuallyEisenstein 𝔪)
    (hnew : heckeGen ⟨q', hq'⟩ ^ 2 - 1 ∈ 𝔪)
    (hq'1 : ¬ (p : ℤ) ∣ (q' : ℤ) - 1)
    (hq1 : (p : ℤ) ∣ (q : ℤ) - 1)
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')
    (A₂ : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A₂)] [CharP (IsLocalRing.ResidueField ↥A₂) q]
    [Fintype ↥(ssPlaces q (N * q') (IsLocalRing.ResidueField ↥A₂))]
    [Fintype ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂))]
    [DecidableEq ↥(ssPlaces q (N * q') (IsLocalRing.ResidueField ↥A₂))]
    [DecidableEq ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂))]
    (X₂ : SSLevelDatum q (IsLocalRing.ResidueField ↥A₂) N q') (hX₂ : X₂.HeckeLaws)
    {Yo₂ : Type} [AddCommGroup Yo₂] [Module HeckeAlg Yo₂] [Module.Finite ℤ Yo₂]
    (eY₂ : Yo₂ ≃+ ↥(CerednikDrinfeld.ribbonKernel X₂.degeneracyData))
    (hY₂ : ∀ (ℓ : Nat.Primes) (m : Yo₂),
      eY₂ (heckeGen ℓ • m) = CerednikDrinfeld.heckeKernelMap X₂.heckeData ℓ (eY₂ m))
    {Xo₂ : Type} [AddCommGroup Xo₂] [Module HeckeAlg Xo₂] [Module.Finite ℤ Xo₂]
    (eX₂ : Xo₂ ≃+ (↥(characterLattice ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂))) × ↥(characterLattice ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)))))
    (hT₂ : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q' → ∀ x : Xo₂,
        ((eX₂ (heckeGen ℓ • x)).1 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) = (X₂.vertexHecke ℓ).mulVec ((eX₂ x).1 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) ∧
        ((eX₂ (heckeGen ℓ • x)).2 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) = (X₂.vertexHecke ℓ).mulVec ((eX₂ x).2 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ))
    (hU₂ : ∀ x : Xo₂,
        ((eX₂ (heckeGen ⟨q', hq'⟩ • x)).1 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) =
            (X₂.vertexHecke ⟨q', hq'⟩).mulVec ((eX₂ x).1 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) - ((eX₂ x).2 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) ∧
        ((eX₂ (heckeGen ⟨q', hq'⟩ • x)).2 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ) = ((q' : ℕ) : ℤ) • ((eX₂ x).1 : ↥(ssPlaces q N (IsLocalRing.ResidueField ↥A₂)) → ℤ))
    {E₂ V₂ : Type} [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₂ : CerednikDrinfeld.DegeneracyData E₂ V₂} {H₂ : CerednikDrinfeld.HeckeData D₂}
    (𝒥 : CerednikDrinfeld.TwoPlaceTorsionDatum p X₂.degeneracyData X₂.heckeData D₂ H₂ A₁ A₂)
    (hL : 𝒥.fst.LocalLaws q') :
    Nat.card (HeckeAlg ⧸ 𝔪) ^
        (Module.finrank (HeckeAlg ⧸ 𝔪) (Xo₂ ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Xo₂))) +
          Module.finrank (HeckeAlg ⧸ 𝔪) (Yo₂ ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Yo₂)))) ≤
      Nat.card ↥(𝒥.fst.W 𝔪) := by sorry
