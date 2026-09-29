-- Prove2me | Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
-- name    : ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/b222066f-2929-5fa8-b798-301ea061b0b8
-- title:
--   Slash by Γ₀(M) has integral q-expansion after scaling
-- statement:
--   Let $M$ be a positive natural number, $k$ an integer, and let $f$ be a modular form of weight $k$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ obtained as the image of $\Gamma_1(M) \le \mathrm{SL}_2(\mathbb{Z})$. Suppose $p \in \mathbb{Z}[[X]]$ satisfies [`ModularCurve.IsIntegralQExp f p`](def/ModularCurve_X1.html#L37), that is, the image of $p$ under the coefficientwise map $\mathbb{Z} \to \mathbb{C}$ equals the $q$-expansion of $f$ of width $1$ (so $f$ has integral Fourier coefficients at $\infty$, with $p$ the generating series). Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M)$. Then there exist a nonzero integer $D$, a modular form $f_1$ of weight $k$ for the same subgroup coming from $\Gamma_1(M)$, and a power series $p_1 \in \mathbb{Z}[[X]]$, such that the image of $p_1$ in $\mathbb{C}[[X]]$ is the width-$1$ $q$-expansion of $f_1$, and such that, as functions on the upper half-plane, $f_1 = D \cdot (f \mid_k \gamma)$, the weight-$k$ slash of $f$ by $\gamma$. Thus the slash of $f$ by an element of $\Gamma_0(M)$ has Fourier coefficients at $\infty$ that are rational with a common bounded denominator $D$.
--
--   The slash of $f$ by $\gamma \in \Gamma_0(M)$ is the action of the diamond operator $\langle \delta \rangle$, $\delta$ the lower-right entry of $\gamma$, on forms of level $M$; the statement records that this action preserves integrality of Fourier expansions up to a nonzero integer denominator. It is used in the construction of the integral/rational structure on the modular curve $X_1(M)$ and on spaces of forms of level $M$, in particular in the treatment of the diamond automorphisms of $X_1(M)$ and in the integrality statements for $q$-expansions of cusp forms twisted by such operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ (D : ℤ) (f₁ : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
      (p₁ : PowerSeries ℤ), D ≠ 0 ∧ ModularCurve.IsIntegralQExp f₁ p₁ ∧
        (⇑f₁ : UpperHalfPlane → ℂ) = (D : ℂ) • ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) := by sorry
