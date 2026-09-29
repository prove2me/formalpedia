-- Prove2me | Theorems.Thm_ModularCurve_heckeDiffModLH_mem_ssPolarDifferentials_and_residue_eq_sum_fiberAlong_of_prime
-- name    : ModularCurve.heckeDiffModLH_mem_ssPolarDifferentials_and_residue_eq_sum_fiberAlong_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/2a13c822-3408-5533-a391-be495b469cbd
-- title:
--   Hecke correspondence preserves supersingular-polar differentials, transforming residues
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$ with $p$ prime, let $N \ge 1$ satisfy $p \nmid N$, let $H' \le (\mathbb{Z}/N)^\times$, and let $\ell$ be a prime with $\ell \ne 0$ in $K$. Write $F =$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')`](def/ModularCurve_X1.html#L101), the subfield of $K((q))$ generated over $K$ by the integral-form ratios for the group $\Gamma_{H'}(N)$, and $F_\ell$ for the corresponding field at level $\Gamma_{H'}(N) \sqcap \Gamma_0(N\ell)$. Let $V =$ [`ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p`](def/ModularCurve_XHDifferentialsModL.html#L35), the submodule `polarDifferentials` of $\Omega[F/K]$ attached to the set `ssPlacesQExp` of places $v$ of $F$ with `IsSSPlaceQExp K _ p v`. Suppose given a $K$-linear map `res` from $V$ to $K$-valued functions on the places of $F$ such that for $\omega \in V$ and $v$ in `ssPlacesQExp` the value $\mathrm{res}(\omega)(v)$ is a simple residue of $\omega$ at $v$ (there is $f \in F$ with $\omega = f \cdot v.\mathrm{dCoord}$ and $v$ takes the value $\mathrm{res}(\omega)(v)$ on $\pi_v f$), and $\mathrm{res}(\omega)(v) = 0$ for all other $v$. Assume the two degeneracy embeddings $\alpha =$ `heckeAlphaModLH` (the inclusion $F \to F_\ell$) and $\beta =$ `heckeBetaModLH` are integral, and that $F_\ell$ has principal divisors. Then the operator `heckeDiffModLH`, namely the differential correspondence $\mathrm{tr}_\beta \circ \alpha^*$, maps $V$ into $V$; and whenever $\omega, \omega' \in V$ satisfy $\omega' = \mathrm{tr}_\beta(\alpha^*\omega)$, then for every place $v$ of $F$ $$\mathrm{res}(\omega')(v) = \sum_{w \in \mathrm{fiberAlong}(\beta, v)} e_\alpha(w)\, \mathrm{res}(\omega)(w|_\alpha),$$ the sum over the finite set of places $w$ of $F_\ell$ restricting to $v$ along $\beta$, with $e_\alpha(w)$ the ramification index of $w$ along $\alpha$, its image in $K$ taken.
--
--   This is the residue-equivariance of the Hecke correspondence at level $\Gamma_{H'}(N) \cap \Gamma_0(N\ell)$: the operator $\mathrm{tr}_\beta \circ \alpha^*$ on differentials with at most simple poles along the supersingular places acts on residues through the explicit weighted fibre map determined by the two degeneracy embeddings. It feeds the counting arguments comparing ranks of residue images of supersingular-polar differentials with point counts on the relevant modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeDiffModLH_mem_ssPolarDifferentials_and_residue_eq_sum_fiberAlong_of_prime.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open AlgebraicCurve

theorem ModularCurve.heckeDiffModLH_mem_ssPolarDifferentials_and_residue_eq_sum_fiberAlong_of_prime
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)

    (res : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p) →ₗ[K]
      (AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) → K))
    (hres : ∀ (ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p))
      (v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
      v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p →
        v.HasSimpleResidue (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) (res ω v))
    (hres0 : ∀ (ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p))
      (v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
      v ∉ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p → res ω v = 0)
    (hα : (ModularCurve.heckeAlphaModLH K N H' ℓ).toRingHom.IsIntegral)
    (hβ : (ModularCurve.heckeBetaModLH K N H' ℓ).toRingHom.IsIntegral)
    [AlgebraicCurve.HasPrincipalDivisors K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))] :
    (∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p),
        ModularCurve.heckeDiffModLH K N H' ℓ (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) ∈
          ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p) ∧
    (∀ (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p)),
        (ω' : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) =
          ModularCurve.heckeDiffModLH K N H' ℓ (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) →
        ∀ v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
          res ω' v =
            ∑ w ∈ AlgebraicCurve.Place.fiberAlong (ModularCurve.heckeBetaModLH K N H' ℓ) hβ v,
              (AlgebraicCurve.Place.ramificationIndexAlong (ModularCurve.heckeAlphaModLH K N H' ℓ) w : K) *
                res ω (AlgebraicCurve.Place.restrictAlong (ModularCurve.heckeAlphaModLH K N H' ℓ) hα w)) := by sorry
