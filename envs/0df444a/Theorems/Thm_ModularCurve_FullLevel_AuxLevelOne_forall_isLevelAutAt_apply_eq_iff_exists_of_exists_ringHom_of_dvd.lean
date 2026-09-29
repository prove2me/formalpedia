-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/588edf8b-0f2c-5224-b3b0-66129e64bcb3
-- title:
--   Fixed field of the Γ(q)∩Γ₀(M') level automorphisms on K
-- statement:
--   Let $q$ be a prime, $M'$ a nonzero natural number with $q \nmid M'$, and $\ell$ a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic $0$ and $\zeta \in L$ a primitive $q$-th root of unity, and assume there is a ring homomorphism $\iota_0 : L \to \mathbb{C}$ with $\iota_0(\zeta) = \exp(2\pi i/q)$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, with the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$, and let $K = L \cdot F_{H_1}$ be the intermediate field of $L((X))$ generated over $L$ by the coefficientwise image of the $q$-expansion field [`ModularCurve.xHFunctionField (q ^ 2 * M') H₁`](def/ModularCurve_XH.html#L79) $\subseteq \mathbb{Q}((X))$ of [`CohCarrier.GammaH (q ^ 2 * M') H₁`](def/CohCarrier_Level.html#L133). Write $F_0 = L \cdot F_{H_q}$ for the analogous field attached to [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) at the same level $q^2M'$. Then: (i) every element of $F_0$ lies in $K$; and (ii) for $w \in K$, one has $\tau(w) = w$ for every $\gamma \in \Gamma(q) \cap \Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ with [`ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) — i.e. $\tau$ acts on every quotient of integral $q$-expansions of weight-$k$ forms on [`CohCarrier.GammaH (q ^ 2 * M') H₁`](def/CohCarrier_Level.html#L133) by the slash action of $\gamma^{-1}$ conjugated by $\mathrm{diag}(q,1)$, after any embedding $\iota : L \to \mathbb{C}$ sending $\zeta$ to $\exp(2\pi i/q)$ — if and only if the Laurent series underlying $w$ lies in $F_0$.
--
--   This identifies the fixed field of the $\Gamma(q)\cap\Gamma_0(M')$ level automorphisms of the function field of $X_{H_1}(q^2M')$ as the function field of $X_{H_q}(q^2M')$, the $\mathrm{diag}(q,1)$-conjugate model of $\Gamma(q)\cap\Gamma_0(M')$, both realised as fields of $q$-expansions at a common level. It is the descent step used by the auxiliary level-one results on Drinfeld charts, modular unit series and Igusa valuations that invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevelOne.forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)) :
    (∀ x : LaurentSeries L,
      x ∈ ModularCurve.laurentBaseChange L
            (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) →
        x ∈ K) ∧
    (∀ w : ↥K,
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            τ w = w) ↔
        ∃ x : LaurentSeries L,
          x ∈ ModularCurve.laurentBaseChange L
            (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) ∧
          ((w : ↥K) : LaurentSeries L) = x) := by sorry
