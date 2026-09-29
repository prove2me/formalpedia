-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.Diamond.mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/97e11544-20bd-5c9d-b73d-eb5c11437889
-- title:
--   Level-q functions fixed by Γ(q)∩Γ₀(M')-level automorphisms
-- statement:
--   Let $q$ be a prime, let $M'\ge 1$ with $q\nmid M'$, and let $\ell_g$ be a prime with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic $0$, let $\zeta\in L$ be a primitive $q$-th root of unity, and assume there is a ring homomorphism $\iota_0:L\to\mathbb C$ with $\iota_0(\zeta)=e^{2\pi i/q}$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of `levelH` $q\,M'$, the kernel of reduction $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$, with the kernel of reduction $(\mathbb Z/q^2M')^\times\to(\mathbb Z/\ell_g)^\times$ (using $\ell_g\mid q^2M'$), and let $K\subseteq L(\!(\mathsf q)\!)$ be the intermediate field generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$ over $\mathbb Q$. The assertion is that every $x$ in the corresponding base-changed function field for `levelH` $q\,M'$ lies in $K$, and that for every $w\in K$ with underlying Laurent series $x$, every $\gamma\in SL_2(\mathbb Z)$ lying in both $\Gamma(q)$ and $\Gamma_0(M')$, and every $L$-algebra automorphism $\tau$ of $K$ satisfying `IsLevelAutAt` $L\,q\,\zeta\,q\,(q^2M')\,H_1\,\gamma^{-1}\,K$ — i.e. for all weights $k$, all weight-$k$ modular forms $f,g$ for $\Gamma_{H_1}(q^2M')$ admitting integral $q$-expansions $p_f,p_g$ with the Laurent series of $p_g$ nonzero, all $x'\in K$ whose Laurent series is the image of $p_f/p_g$, and all $\iota:L\to\mathbb C$ with $\iota(\zeta)=e^{2\pi i/q}$, one has $\iota(\tau x')\cdot (g\mid_k \gamma^{-1,\sharp})^{\wedge}=(f\mid_k \gamma^{-1,\sharp})^{\wedge}$ as $q$-expansions, where $\delta^{\sharp}=\mathrm{diag}(1,q)\,\delta\,\mathrm{diag}(1,q)^{-1}$ — one has $\tau w=w$.
--
--   This is the fixed-field step for level automorphisms: functions of the larger level $H=\ker((\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times)$ sit inside the $H_1$-level field and are invariant under every automorphism attached to an element of $\Gamma(q)\cap\Gamma_0(M')$, the auxiliary prime $\ell_g\equiv 11\pmod{12}$ serving to cut the level down to a $\Gamma_1(\ell_g)$-type frame. It is used by the auxiliary-level lemmas producing invariant elements and ring homomorphisms on invariants over valuation subrings of the function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.mem_and_apply_eq_of_isLevelAutAt_of_mem_Gamma_of_eq_levelH_inf_ker
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)) :
    ∀ x : LaurentSeries L,
      x ∈ ModularCurve.laurentBaseChange L
            (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) →
      x ∈ K ∧
      ∀ w : ↥K, ((w : ↥K) : LaurentSeries L) = x →
        ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            τ w = w := by sorry
