-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/92ed4977-1d34-55c0-90ef-ffce33e08079
-- title:
--   Rational decomposition of f∣γ'^{sharp} on Γ_{H_1}(m²M')
-- statement:
--   Let $m,M'\ge 1$ be coprime, let $\ell_g\mid M'$, put $N=m^2M'$, and let $H_1\le(\mathbb Z/N)^\times$ be the intersection of the kernel of reduction $(\mathbb Z/N)^\times\to(\mathbb Z/m)^\times$ with the kernel of reduction $(\mathbb Z/N)^\times\to(\mathbb Z/\ell_g)^\times$, i.e. the units $\equiv 1$ modulo $m$ and modulo $\ell_g$. Write $\Gamma_{H_1}(N)$ for the subgroup of $\mathrm{SL}_2(\mathbb Z)$ consisting of the $\gamma\in\Gamma_0(N)$ whose lower right entry, reduced modulo $N$, lies in $H_1$, viewed inside $\mathrm{GL}_2(\mathbb R)$. Let $k$ be an even integer, let $f$ be a modular form of weight $k$ for $\Gamma_{H_1}(N)$ all of whose $q$-expansion coefficients at width $1$ are rational, and let $\gamma\in\Gamma_0(M')$. Then there is a family $(h_j)_{j\in\mathbb N}$ of weight-$k$ modular forms for $\Gamma_{H_1}(N)$, again with rational $q$-expansion coefficients at width $1$, such that for every natural number $s$ coprime to $m$ and every $\gamma'\in\Gamma_0(M')$ whose lower right entry agrees with that of $\gamma$ modulo $\ell_g$ and which satisfies $\mathrm{diag}(1,s)\,\gamma'=\gamma\,\mathrm{diag}(1,s)$ in $M_2(\mathbb Z/m)$, one has, as functions on the upper half-plane,
--   $$f\,\big|_k\,\big(\mathrm{diag}(m,1)^{-1}\gamma'\,\mathrm{diag}(m,1)\big)=\sum_{j=0}^{m-1}e^{2\pi i sj/m}\,h_j.$$
--   The forms $h_j$ depend on $f$ and $\gamma$ only, not on $s$ or $\gamma'$.
--
--   This is a Shimura-reciprocity statement for the Galois action on $q$-expansions, transported to the conjugated full level $\Gamma_{H_1}(m^2M')$ with the extra guard at $\ell_g$ needed because a $\Gamma_{H_1}$-form is acted on by the diamond operator $\langle d_{\gamma'}\bmod\ell_g\rangle$. It feeds the analysis of level automorphisms of the full-level modular curve, in particular the characterisations of the maps $\mathrm{isLevelAutAt}$ and their conjugates by primitive roots of unity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker.lean

import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

open scoped MatrixGroups ModularForm

theorem ModularCurve.FullLevel.exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker
    (m : ℕ) [NeZero m] (M' : ℕ) [NeZero M'] (hmM' : Nat.Coprime m M')
    (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (m ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH m M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (m ^ 2))).ker)
    {k : ℤ} (hk : Even k)
    (f : ModularForm (CohCarrier.GammaH (m ^ 2 * M') H₁ : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') :
    ∃ h : ℕ → ModularForm (CohCarrier.GammaH (m ^ 2 * M') H₁ : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ j n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 (h j)).coeff n = (r : ℂ)) ∧
      ∀ (s : ℕ) (γ' : SL(2, ℤ)), Nat.Coprime s m → γ' ∈ CongruenceSubgroup.Gamma0 M' →
        ((γ' 1 1 : ℤ) : ZMod ℓg) = ((γ 1 1 : ℤ) : ZMod ℓg) →
        !![(1 : ZMod m), 0; 0, (s : ZMod m)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m)
          = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod m) * !![(1 : ZMod m), 0; 0, (s : ZMod m)] →
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] ModularCurve.FullLevel.conjElemN m γ') =
          ∑ j ∈ Finset.range m,
            Complex.exp (2 * Real.pi * Complex.I * ((s * j : ℕ) : ℂ) / m) •
              (⇑(h j) : UpperHalfPlane → ℂ) := by sorry
