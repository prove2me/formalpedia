-- Prove2me | Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
-- name    : ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/fe6640f4-f025-5455-a866-9bba11379d25
-- title:
--   Diamond action of Γ₀(M) on the q-expansion function field
-- statement:
--   Let $K$ be a field of characteristic zero, $M$ a non-zero natural number and $H\le(\mathbb{Z}/M)^\times$ a subgroup; write $\Gamma_H(M)=$ [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) for the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of the elements of $\Gamma_0(M)$ whose image under the homomorphism $\Gamma_0(M)\to(\mathbb{Z}/M)^\times$, $\gamma\mapsto d_\gamma \bmod M$, lies in $H$. For a subgroup $\Gamma\le\mathrm{SL}_2(\mathbb{Z})$, [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) denotes the intermediate field of $K((q))=$ `LaurentSeries K` generated over $K$ by all quotients $\iota_K(p_f)/\iota_K(p_g)$, where $f,g$ are modular forms of one weight $k$ on the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, $p_f,p_g\in\mathbb{Z}[[q]]$ satisfy `IsIntegralQExp`, i.e. their images in $\mathbb{C}[[q]]$ are the $q$-expansions of $f$ and $g$ at width $1$, $\iota_K$ denotes coefficientwise reduction $\mathbb{Z}[[q]]\to K((q))$, and $\iota_K(p_g)\neq 0$. Write $F_H$ for this field at $\Gamma=\Gamma_H(M)$. The assertion is that there is a monoid (hence group) homomorphism $\rho\colon\Gamma_0(M)\to (F_H\simeq_{K} F_H)$ into the $K$-algebra automorphisms of $F_H$ such that: $\rho(\gamma)=1$ whenever $\gamma\in\Gamma_H(M)$; $\rho(\gamma)=1$ whenever $\gamma=-1$; each $\rho(\gamma)$ fixes every element of $F_H$ whose underlying Laurent series lies in [`ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)`](def/ModularCurve_X1.html#L101); and, for every $\gamma\in\Gamma_0(M)$, every weight $k\in\mathbb{Z}$, all modular forms $f,g,f_1,g_1$ of weight $k$ on $\Gamma_H(M)$ with integral $q$-expansions $p_f,p_g,p_{f_1},p_{g_1}$, and every $c\in\mathbb{C}^\times$ with $f_1=c\,(f\mid_k\gamma)$ and $g_1=c\,(g\mid_k\gamma)$ as functions on the upper half-plane, and $\iota_K(p_g)\neq0$, $\iota_K(p_{g_1})\neq0$, one has $\rho(\gamma)\bigl(\iota_K(p_f)/\iota_K(p_g)\bigr)=\iota_K(p_{f_1})/\iota_K(p_{g_1})$ in $K((q))$.
--
--   This is the diamond (Galois) action of $\Gamma_0(M)$, through $\Gamma_0(M)/\Gamma_H(M)\{\pm1\}$, on the $q$-expansion model of the function field of the modular curve $X_H(M)$, in the characteristic-zero case, where bounded denominators for the translates of integral $q$-expansions suffice to make the action well defined. It feeds the full-level computations of the degree of $F_H$ over the $\Gamma_0(M)$-function field by Artin's theorem on fixed fields; the proof cites the existence of an integral translate $f_1=D\,(f\mid_k\gamma)$ with $D\in\mathbb{Z}\setminus\{0\}$ and the determination of a modular form by its $q$-coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
    (K : Type*) [Field K] [CharZero K] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
          ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      (∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ = 1) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) = -1 → ρ γ = 1) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
        (x : LaurentSeries K) ∈ ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) →
          ρ γ x = x) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) {k : ℤ}
        (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ) (_ : c ≠ 0)
        (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg)
        (_ : ModularCurve.IsIntegralQExp f₁ pf₁) (_ : ModularCurve.IsIntegralQExp g₁ pg₁)
        (_ : (⇑f₁ : UpperHalfPlane → ℂ) =
          c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
        (_ : (⇑g₁ : UpperHalfPlane → ℂ) =
          c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
        (hg0 : ModularCurve.intSeriesC K pg ≠ 0) (_ : ModularCurve.intSeriesC K pg₁ ≠ 0),
          ((ρ γ ⟨ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg,
              ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
                ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
            ModularCurve.intSeriesC K pf₁ / ModularCurve.intSeriesC K pg₁) := by sorry
