-- Prove2me | Theorems.Thm_ModularCurve_twoPlaceTorsionDatum_snd_W_le_toric_of_not_hasLowerLevelTorsion_of_W_le_invariants
-- name    : ModularCurve.twoPlaceTorsionDatum_snd_W_le_toric_of_not_hasLowerLevelTorsion_of_W_le_invariants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/5c84d47c-414f-5f48-a085-b65622693969
-- title:
--   W(𝔪) is toric at the second place
-- statement:
--   Let $p$ be a prime and $N,q,q'$ natural numbers with $q$ and $q'$ prime, $q \nmid N$, $q' \nmid N$, $q' \neq q$, $q' \neq p$, $q' \ge 5$, and $N$, $q$, $q'$, $Nq'$ nonzero. Let $\mathfrak m$ be a maximal ideal of the abstract Hecke algebra `HeckeAlg` $=\mathbb Z[T_\ell:\ell\text{ prime}]$ containing $p$ and not eventually Eisenstein, i.e. there is no finite set $S$ of primes with $T_\ell-(\ell+1)\in\mathfrak m$ for all $\ell\notin S$. Let $A_1$ be a valuation subring of $\overline{\mathbb Q}$ with $q'$ a nonunit in $A_1$, with residue field $\kappa$ of characteristic $q'$, and let $A_2$ be any valuation subring of $\overline{\mathbb Q}$. Assume, for the Hecke module structure `heckeModuleBar` on $J_0(Nq')=\mathrm{Pic}^0$ of the level-$Nq'$ modular function field over $\overline{\mathbb Q}$, that there is no finite set $S$ of primes, all dividing $Nqq'$, admitting a nonzero $y$ killed by every integer lying in $\mathfrak m$ and by every $T_\ell-b$ ($\ell\notin S$, $b\in\mathbb Z$) lying in $\mathfrak m$. Let $X_1$ be a supersingular level datum for $q'$ over $\kappa$ at levels $Nq \rightrightarrows N$ satisfying `HeckeLaws`, the supersingular place sets being finite. Let $D_1$, $H_1$ be degeneracy and Hecke data on finite types $E_1,V_1$, and let $\mathcal J$ be a two-place $p$-torsion datum for $(D_1,H_1)$ and $(X_1.\mathrm{degeneracyData}, X_1.\mathrm{heckeData})$ at $A_1,A_2$: a finite abelian group $T$ killed by $p$ with commuting Hecke and $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ actions of finite level, toric subgroups and specialisation maps at each place. Suppose the second constituent $\mathcal J.\mathrm{snd}$ (the datum at $A_2$ with $D_2=X_1.\mathrm{degeneracyData}$, toric subgroup $\mathrm{toric}_2$ and $\mathrm{sp}_2$) satisfies `LocalLaws` at $q$ — toric points are Hecke-stable and contained in the inertia invariants at $A_2$, the isomorphism with $\mathrm{Hom}(\mathrm{ribbonKernel}\,D_2,\mathbb Z/p)$ is Hecke-equivariant, $\mathrm{sp}_2$ vanishes exactly on the toric points, has image the $p$-torsion of the ribbon component group and is Hecke-equivariant, and for any Frobenius $\varphi$ at $q$ one has $\varphi = q\,T_q$ on toric points while $\varphi - T_q$ lands in the toric subgroup — and that the subgroup $\mathcal J.\mathrm{snd}.W(\mathfrak m)$ of $T$ attached to $\mathfrak m$ is contained in the inertia invariants $\bigcap_{\sigma\in I(A_2)}\ker(\sigma-1)$. Then $\mathcal J.\mathrm{snd}.W(\mathfrak m)$ is contained in $\mathrm{toric}_2$.
--
--   This is the removed-prime half of Ribet's exchange argument on the Shimura curve: absence of lower-level $\mathfrak m$-torsion on $J_0(Nq')$ forces the $\mathfrak m$-part of the torsion datum at the place $A_2$ above $q$ to be entirely toric, so that the specialisation map to the ribbon component group kills it. It feeds the exchange inequalities [`ModularCurve.finrank_quotient_old_add_ribbon_le_finrank_quotient_ribbon_of_twoPlaceTorsionDatum_of_le_invariants`](thm.html#ModularCurve.finrank_quotient_old_add_ribbon_le_finrank_quotient_ribbon_of_twoPlaceTorsionDatum_of_le_invariants) and its variant under a divisibility hypothesis, which compare old and ribbon multiplicities in the $(q,q')$-level switch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_twoPlaceTorsionDatum_snd_W_le_toric_of_not_hasLowerLevelTorsion_of_W_le_invariants.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_MazurPrincipleCore
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.twoPlaceTorsionDatum_snd_W_le_toric_of_not_hasLowerLevelTorsion_of_W_le_invariants
    (p : ℕ) [Fact p.Prime] {N q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hqN : ¬ q ∣ N) (hqq' : q' ≠ q) (hq'p : q' ≠ p)
    (hq'N : ¬ q' ∣ N) [NeZero (N * q')] [NeZero q]
    [NeZero N] [NeZero q'] [Fact q.Prime] [Fact q'.Prime]
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : (p : HeckeAlg) ∈ 𝔪) (heis : ¬ IsEventuallyEisenstein 𝔪)
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')
    (A₂ : ValuationSubring (AlgebraicClosure ℚ))
    (hreg : letI := heckeModuleBar (N * q')
      ¬ ∃ S : Finset Nat.Primes, (∀ ℓ ∈ S, (ℓ : ℕ) ∣ N * q * q') ∧
        HasLowerLevelTorsion S 𝔪 (JZero (N * q')))
    [DecidableEq (IsLocalRing.ResidueField ↥A₁)] [CharP (IsLocalRing.ResidueField ↥A₁) q']
    [Fintype ↥(ssPlaces q' (N * q) (IsLocalRing.ResidueField ↥A₁))]
    [Fintype ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))]
    [DecidableEq ↥(ssPlaces q' (N * q) (IsLocalRing.ResidueField ↥A₁))]
    [DecidableEq ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))]
    (X₁ : SSLevelDatum q' (IsLocalRing.ResidueField ↥A₁) N q) (hX₁ : X₁.HeckeLaws)
    (hq'5 : 5 ≤ q')
    {E₁ V₁ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁]
    {D₁ : CerednikDrinfeld.DegeneracyData E₁ V₁} {H₁ : CerednikDrinfeld.HeckeData D₁}
    (𝒥 : CerednikDrinfeld.TwoPlaceTorsionDatum p D₁ H₁ X₁.degeneracyData X₁.heckeData A₁ A₂)
    (hL : 𝒥.snd.LocalLaws q)
    (hunr : 𝒥.snd.W 𝔪 ≤ 𝒥.snd.invariants) :
    𝒥.snd.W 𝔪 ≤ 𝒥.snd.toric := by sorry
