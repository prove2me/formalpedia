-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_modularForm_gammaH_qExpansion_eq_smul_prod_toricPoint_sub_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.exists_modularForm_gammaH_qExpansion_eq_smul_prod_toricPoint_sub_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/aa5fa3c1-dd12-552c-b990-6788a78dc6d0
-- title:
--   Modular forms on Γ_{H_1}(q²M') with prescribed toric q-expansions
-- statement:
--   Fix nonzero natural numbers $q$ and $M'$, and $\ell_g$ with $3 \le \ell_g$ and $\ell_g \mid M'$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^\times$ (the subgroup [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22)) with the kernel of reduction to $(\mathbb{Z}/\ell_g)^\times$, $\ell_g$ dividing $q^2M'$ through $\ell_g \mid M'$. Let $p$ be prime, $k$ a natural number with $p^k \mid M'$, let $t$ be a natural number coprime to $\ell_g$, and let $c \in \mathbb{Q}$. Put $S = \{\, i : 1 \le i \le p^k/2,\ p \nmid i \,\}$ (natural-number division) and $d = \#S$. Write $X(u)$ for the first coordinate of [`ModularCurve.toricPoint ℂ q u`](def/ModularCurve_TateSlots.html#L125), the Laurent series coming from the power series with constant term $u/(1-u)^2$ and $m$-th coefficient $\sum_{e \mid m,\ q \mid e} (m/e)\bigl(u^{m/e} + u^{-m/e}\bigr) - 2\,[\,q \mid m\,]\sum_{e \mid m/q} e$ for $m \ge 1$, and set $\zeta = e^{2\pi i/\ell_g}$, $\zeta_{p^k} = e^{2\pi i/p^k}$. Then there exist modular forms $\Phi, \Psi$ of weight $2d$ on the subgroup of $\mathrm{GL}_2(\mathbb{R})$ determined by $\Gamma_{H_1}(q^2M')$, namely the image in $\Gamma_0(q^2M')$ of the preimage of $H_1$ under the lower-right-entry character [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121), and a rational $a \ne 0$, such that the $q$-expansions at infinity with period $1$ satisfy $$\widetilde{\Psi} = a\bigl(X(\zeta^t) - X(\zeta^{2t})\bigr)^d, \qquad \widetilde{\Phi} = a\prod_{i \in S}\Bigl(c\bigl(X(\zeta^t) - X(\zeta^{2t})\bigr) - \bigl(X(\zeta_{p^k}^{\,i}) - X(\zeta^t)\bigr)\Bigr),$$ with the same $a$ in both identities.
--
--   This is the diamond-level version of the construction of modular forms out of products of shifted Weierstrass division values: the weight-$2$ building blocks $12\,\wp(s/n)/(2\pi i)^2$ on $\Gamma_1(n)$ are combined so that the resulting forms of weight $2d$ on $\Gamma_{H_1}(q^2M')$ have $q$-expansions equal to prescribed polynomial expressions in abscissae of toric points of the Tate curve with parameter $\mathfrak{q}^q$, the auxiliary points being the $\ell_g$-torsion points $\zeta^t, \zeta^{2t}$. It is used in the comparison of coefficients of variable changes with the span of the rigid data at level $H_1$, in [`ModularCurve.FullLevel.Diamond.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_fst_mem_range_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_fst_mem_range_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_modularForm_gammaH_qExpansion_eq_smul_prod_toricPoint_sub_rigidDataH1Pow.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.FullLevel.Diamond.exists_modularForm_gammaH_qExpansion_eq_smul_prod_toricPoint_sub_rigidDataH1Pow
    (q : ℕ) [NeZero q] (M' : ℕ) [NeZero M'] (ℓg : ℕ) (hℓg : 3 ≤ ℓg) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M')
    (t : ℕ) (ht : t.Coprime ℓg) (c : ℚ) :
    ∃ (Φ Ψ : ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
        Subgroup (GL (Fin 2) ℝ)) (2 * (((Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i)).card : ℕ) : ℤ))
      (a : ℚ), a ≠ 0 ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Ψ) =
        (a : ℂ) • ((ModularCurve.toricPoint ℂ q (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ t)).1 -
          (ModularCurve.toricPoint ℂ q (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ (2 * t))).1) ^
            ((Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i)).card ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Φ) =
        (a : ℂ) • ∏ i ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i),
          ((c : ℂ) • ((ModularCurve.toricPoint ℂ q (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ t)).1 -
              (ModularCurve.toricPoint ℂ q (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ (2 * t))).1) -
            ((ModularCurve.toricPoint ℂ q (Complex.exp (2 * Real.pi * Complex.I / ((p ^ k : ℕ) : ℂ)) ^ i)).1 -
              (ModularCurve.toricPoint ℂ q (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ t)).1)) := by sorry
