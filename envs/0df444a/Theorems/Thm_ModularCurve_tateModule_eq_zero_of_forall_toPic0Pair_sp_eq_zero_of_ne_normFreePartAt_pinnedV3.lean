-- Prove2me | Theorems.Thm_ModularCurve_tateModule_eq_zero_of_forall_toPic0Pair_sp_eq_zero_of_ne_normFreePartAt_pinnedV3
-- name    : ModularCurve.tateModule_eq_zero_of_forall_toPic0Pair_sp_eq_zero_of_ne_normFreePartAt_pinnedV3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/cf7ebd7e-9ed1-547b-9bd0-0dd7cade7747
-- title:
--   Vanishing of ℓ-adic Tate sequences with trivial Igusa specialisation
-- statement:
--   Fix a nonzero natural number $M$ and a prime $p$ with $p \mid M$ and $p^2 \nmid M$, and a valuation subring $P$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $P$ (i.e. $P$ lies over $p$). Call a subgroup $I$ of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ *admissible* when $I$ is contained in the inertia subgroup of $P$ over $\mathbb Q$, every $\sigma \in I$ fixes every $p$-th root of unity, and $I$ has finite index in that inertia subgroup. Let $\mathcal D$ assign to each admissible $I$ a datum $\mathcal D_I$ of type `QExpSemistableSpecializationPinnedV3` for the $q$-expansion function field `x1FunctionField M`, the place $P$, the group $I$ and the number $p$, with residue field $\kappa =$ `IsLocalRing.ResidueField P` and residue map of $P$, and with the pinning data `x1FunctionFieldC κ M`, `x1FunctionField (M / p)`, `x1FunctionFieldC κ (M / p)`; such a datum consists of a finite set `nodes` of pairs of places of the base-changed function field over $\kappa$ with rational residue fields, a semilinear automorphism `frob` raising $q$-expansion coefficients to the $p$-th power, an additive subgroup `dom` of $\mathrm{Pic}^0$ of `laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField M)` (the group $J_1(M)$) on which $I$ acts trivially and which is stable under Frobenius elements normalising $I$, a homomorphism `sp` from `dom` to the glued $\mathrm{Pic}^0$ attached to `nodes`, together with injectivity, surjectivity, torsion-counting and Frobenius-compatibility clauses, summarised here. Assume two compatibility hypotheses on $\mathcal D$: (i) for admissible $I' \le I$ and every $y$ in the domain of $\mathcal D_I$, the element $y$ also lies in the domain of $\mathcal D_{I'}$ and the two images of $y$ under `sp` followed by [`AlgebraicCurve.GluedPic0.toPic0Pair`](def/AlgebraicCurve_GluedPic0.html#L229) (into a product of two $\mathrm{Pic}^0$ groups) coincide; (ii) for each admissible $I$, every $y$ in [`ModularCurve.normFreePartAt M p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) — the image of the endomorphism `normFreeEnd M (normFreeRepsAt M p)` of $J_1(M)$ — that is fixed by all $\sigma \in I$ lies in the domain of $\mathcal D_I$. The conclusion: for every prime $\ell \ne p$ and every element $x$ of [`TateModule ℓ (JOne M)`](def/EllipticCurve_TateModule.html#L15), that is every sequence $(x_n)_{n \in \mathbb N}$ in $J_1(M)$ with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$, if each $x_n$ lies in `normFreePartAt M p` and, for every $n$ and every admissible $I$ with $x_n$ in the domain of $\mathcal D_I$, the image of $x_n$ under `sp` followed by `toPic0Pair` is $0$, then $x = 0$.
--
--   This is the injectivity statement, for residue characteristic $\ell$ different from $p$, of the two-component specialisation map of a family of pinned $q$-expansion semistable specialisation data on the norm-free part of $J_1(M)$: no nonzero $\ell$-adic Tate sequence lying in the norm-free part can have trivial reduction in both Igusa components. It is used in the Tate-module identities [`ModularCurve.rep_diamondGen_apply_inertia_sub_eq_of_nsmul_sub_sum_tateModule_jOne_of_dvd_of_not_sq_dvd_of_le_div`](thm.html#ModularCurve.rep_diamondGen_apply_inertia_sub_eq_of_nsmul_sub_sum_tateModule_jOne_of_dvd_of_not_sq_dvd_of_le_div) and [`ModularCurve.rep_frobenius_rep_heckeGenOne_sub_smul_rep_diamondGen_rep_inertia_sub_eq_zero_normFreePartAt_tateModule_jOne_of_le_div`](thm.html#ModularCurve.rep_frobenius_rep_heckeGenOne_sub_smul_rep_diamondGen_rep_inertia_sub_eq_zero_normFreePartAt_tateModule_jOne_of_le_div), which compare Frobenius, Hecke and diamond operators on the norm-free part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_tateModule_eq_zero_of_forall_toPic0Pair_sp_eq_zero_of_ne_normFreePartAt_pinnedV3.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import Definitions.Def_ModularCurve_QExpSemistableSpecializationPinnedV3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem ModularCurve.tateModule_eq_zero_of_forall_toPic0Pair_sp_eq_zero_of_ne_normFreePartAt_pinnedV3
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (𝒟 : ∀ I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        I ≤ P.inertiaSubgroupIn ℚ →
        (∀ σ ∈ I, ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ) →
        (I.subgroupOf (P.inertiaSubgroupIn ℚ)).FiniteIndex →
        ModularCurve.QExpSemistableSpecializationPinnedV3 (ModularCurve.x1FunctionField M) P I p
          (IsLocalRing.ResidueField P) (IsLocalRing.residue P)
          (ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField P) M)
          (ModularCurve.x1FunctionField (M / p))
          (ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField P) (M / p))) :

    (∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ P.inertiaSubgroupIn ℚ)
          (hIμ : ∀ σ ∈ I, ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ)
          (hIf : (I.subgroupOf (P.inertiaSubgroupIn ℚ)).FiniteIndex)
          (I' : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI' : I' ≤ P.inertiaSubgroupIn ℚ)
          (hI'μ : ∀ σ ∈ I', ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ)
          (hI'f : (I'.subgroupOf (P.inertiaSubgroupIn ℚ)).FiniteIndex),
        I' ≤ I →
        ∀ (y : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ)
            (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)))
          (hy : y ∈ (𝒟 I hI hIμ hIf).dom), ∃ h' : y ∈ (𝒟 I' hI' hI'μ hI'f).dom,
          AlgebraicCurve.GluedPic0.toPic0Pair _ ((𝒟 I' hI' hI'μ hI'f).sp ⟨y, h'⟩) =
            AlgebraicCurve.GluedPic0.toPic0Pair _ ((𝒟 I hI hIμ hIf).sp ⟨y, hy⟩)) →

    (∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ P.inertiaSubgroupIn ℚ)
          (hIμ : ∀ σ ∈ I, ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ)
          (hIf : (I.subgroupOf (P.inertiaSubgroupIn ℚ)).FiniteIndex),
        ∀ y ∈ ModularCurve.normFreePartAt M p, (∀ σ ∈ I, σ • y = y) → y ∈ (𝒟 I hI hIμ hIf).dom) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
      ∀ x : TateModule ℓ (ModularCurve.JOne M),
        (∀ n : ℕ, (x : ℕ → ModularCurve.JOne M) n ∈ ModularCurve.normFreePartAt M p) →
        (∀ (n : ℕ) (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
            (hI : I ≤ P.inertiaSubgroupIn ℚ)
            (hIμ : ∀ σ ∈ I, ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ)
            (hIf : (I.subgroupOf (P.inertiaSubgroupIn ℚ)).FiniteIndex)
            (h : (x : ℕ → ModularCurve.JOne M) n ∈ (𝒟 I hI hIμ hIf).dom),
            AlgebraicCurve.GluedPic0.toPic0Pair _ ((𝒟 I hI hIμ hIf).sp ⟨_, h⟩) = 0) →
        x = 0 := by sorry
