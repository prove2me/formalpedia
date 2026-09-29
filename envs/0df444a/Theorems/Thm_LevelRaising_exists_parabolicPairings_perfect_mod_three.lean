-- Prove2me | Theorems.Thm_LevelRaising_exists_parabolicPairings_perfect_mod_three
-- name    : LevelRaising.exists_parabolicPairings_perfect_mod_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/b6108e2c-1807-56ed-b36c-b1114c62d6a7
-- title:
--   Integral pairings mod 3 with Hecke and degeneracy adjunctions
-- statement:
--   Let $N,q$ be nonzero naturals with $q$ prime and $q \nmid N$, and write $L_M$ for [`ModularCurve.Period.parabolicHoms ℤ (Gamma0 M) ℤ`](def/ModularCurve_PeriodMap.html#L62), the $\mathbb{Z}$-submodule of additive homomorphisms $\varphi : \mathrm{Additive}(\Gamma_0(M)) \to \mathbb{Z}$ vanishing on every $\gamma$ whose matrix satisfies $(\operatorname{tr}\gamma)^2 = 4$. Four hypotheses say that the relevant operators preserve this vanishing condition: the Hecke operator [`HeckeEis.heckeOperatorHom M ℓ ℤ`](def/Gamma0HeckeOperatorHom.html#L285) (the transfer from the subgroup [`HeckeEis.heckeUpper M ℓ`](def/Gamma0HeckeOperatorHom.html#L128) composed with pullback along [`HeckeEis.heckeConj M ℓ`](def/Gamma0HeckeOperatorHom.html#L172)) does so at every level $M$ and every nonzero $\ell$; the pullbacks along [`Ihara.ι₀ N q`](def/IharaIota.html#L17) and [`Ihara.ι₁ N q`](def/IharaIota.html#L111) map $L_N$ into $L_{Nq}$; and [`HeckeEis.degeneracyTransfer₀ N q ℤ hq hqN`](def/HeckeEis_DegeneracyTransfers.html#L195), [`HeckeEis.degeneracyTransfer₁ N q ℤ`](def/HeckeEis_DegeneracyTransfers.html#L99) map $L_{Nq}$ into $L_N$. The conclusion asserts the existence of $\mathbb{Z}$-bilinear forms $\mathrm{pair}_1$ on $L_{Nq}$ and $\mathrm{pair}_0$ on $L_N$ such that: each is perfect modulo $3$ in both variables (if $3$ divides $\langle x,y\rangle$ for all $y$ then $x \in 3L$, and symmetrically); for every prime $\ell \nmid Nq$ the Hecke operator is self-adjoint for $\mathrm{pair}_1$ and for $\mathrm{pair}_0$ (for $\mathrm{pair}_0$ only under $\ell \nmid Nq$, not merely $\ell \nmid N$); and each degeneracy transfer is adjoint to the corresponding pullback, i.e. $\mathrm{pair}_0(\beta_i x, y) = \mathrm{pair}_1(x, \iota_i^* y)$ for $i = 0,1$.
--
--   This packages the Poincaré-duality input for level raising: the intersection pairing on the parabolic cohomology of $\Gamma_0(N)$ and $\Gamma_0(Nq)$, normalised so as to be perfect modulo $3$, with Hecke operators away from $Nq$ self-adjoint and the two degeneracy transfers adjoint to the two degeneracy pullbacks. It is used in the analysis of the $q$-new support of normalised eigenforms, via [`LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime`](thm.html#LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LevelRaising_exists_parabolicPairings_perfect_mod_three.lean

import Definitions.Def_HeckeEis_DegeneracyTransfers
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem LevelRaising.exists_parabolicPairings_perfect_mod_three
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (hTpar : ∀ (M ℓ : ℕ) [NeZero ℓ] (φ : Additive (Gamma0 M) →+ ℤ),
      ModularCurve.Period.IsParabolicHom (Gamma0 M) φ →
        ModularCurve.Period.IsParabolicHom (Gamma0 M) (HeckeEis.heckeOperatorHom M ℓ ℤ φ))
    (hrespar₀ : ∀ y ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      HeckeEis.pullbackHom (Ihara.ι₀ N q) y ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ)
    (hrespar₁ : ∀ y ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
      HeckeEis.pullbackHom (Ihara.ι₁ N q) y ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ)
    (hβpar₀ : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ,
      HeckeEis.degeneracyTransfer₀ N q ℤ hq hqN x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
    (hβpar₁ : ∀ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ,
      HeckeEis.degeneracyTransfer₁ N q ℤ x ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ) :
    ∃ (pair₁ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ →ₗ[ℤ] ℤ)
      (pair₀ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ] ℤ),
      ((∀ x, (∀ y, (3 : ℤ) ∣ pair₁ x y) → ∃ x', x = (3 : ℤ) • x') ∧
        (∀ y, (∀ x, (3 : ℤ) ∣ pair₁ x y) → ∃ y', y = (3 : ℤ) • y')) ∧
      ((∀ x, (∀ y, (3 : ℤ) ∣ pair₀ x y) → ∃ x', x = (3 : ℤ) • x') ∧
        (∀ y, (∀ x, (3 : ℤ) ∣ pair₀ x y) → ∃ y', y = (3 : ℤ) • y')) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q →
        ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ,
          pair₁ ⟨HeckeEis.heckeOperatorHom (N * q) ℓ ℤ x, hTpar (N * q) ℓ x x.2⟩ y =
            pair₁ x ⟨HeckeEis.heckeOperatorHom (N * q) ℓ ℤ y, hTpar (N * q) ℓ y y.2⟩) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q →
        ∀ x y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ,
          pair₀ ⟨HeckeEis.heckeOperatorHom N ℓ ℤ x, hTpar N ℓ x x.2⟩ y =
            pair₀ x ⟨HeckeEis.heckeOperatorHom N ℓ ℤ y, hTpar N ℓ y y.2⟩) ∧
      (∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ)
        (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
          pair₀ ⟨HeckeEis.degeneracyTransfer₀ N q ℤ hq hqN x, hβpar₀ x x.2⟩ y =
            pair₁ x ⟨HeckeEis.pullbackHom (Ihara.ι₀ N q) y, hrespar₀ y y.2⟩) ∧
      (∀ (x : ModularCurve.Period.parabolicHoms ℤ (Gamma0 (N * q)) ℤ)
        (y : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ),
          pair₀ ⟨HeckeEis.degeneracyTransfer₁ N q ℤ x, hβpar₁ x x.2⟩ y =
            pair₁ x ⟨HeckeEis.pullbackHom (Ihara.ι₁ N q) y, hrespar₁ y y.2⟩) := by sorry
