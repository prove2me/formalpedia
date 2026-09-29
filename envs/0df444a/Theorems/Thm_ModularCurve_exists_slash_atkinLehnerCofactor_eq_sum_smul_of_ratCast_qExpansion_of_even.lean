-- Prove2me | Theorems.Thm_ModularCurve_exists_slash_atkinLehnerCofactor_eq_sum_smul_of_ratCast_qExpansion_of_even
-- name    : ModularCurve.exists_slash_atkinLehnerCofactor_eq_sum_smul_of_ratCast_qExpansion_of_even
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/ec8b4450-3745-5d6c-8172-cf3ae391c95d
-- title:
--   Atkin–Lehner transform at the cofactor of a rational even-weight form
-- statement:
--   Let $p$ be prime, $M\ge 1$ with $p \mid M$ and $p^2 \nmid M$, and write $Q = M/p$. Let $H \le (\mathbb{Z}/M)^\times$ be a subgroup such that every unit of $\mathbb{Z}/M$ whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/Q)^\times$ is trivial lies in $H$; here $\Gamma_H(M)$ denotes the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those $\gamma \in \Gamma_0(M)$ whose lower-right entry, reduced modulo $M$, defines a unit lying in $H$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Let $x,y,z,w \in \mathbb{Z}$ satisfy $Qxw - pyz = 1$ and let $W \in \mathrm{GL}_2(\mathbb{R})$ have underlying matrix $\begin{pmatrix} Qx & y \\ Mz & Qw\end{pmatrix}$ (so $\det W = Q$). Let $k$ be an even integer and $f$ a modular form of weight $k$ on $\Gamma_H(M)$ each of whose $q$-expansion coefficients at $\infty$ (width $1$) is the image of a rational number, and let $\iota : \overline{\mathbb{Q}} \to \mathbb{C}$ be a ring homomorphism. Then there exist $n \in \mathbb{N}$, scalars $c_i \in \overline{\mathbb{Q}}$, modular forms $g_i$ of weight $k$ on $\Gamma_H(M)$ and integral power series $p_i \in \mathbb{Z}[[q]]$ $(i \in \mathrm{Fin}\,n)$ such that the image of $p_i$ in $\mathbb{C}[[q]]$ is the width-$1$ $q$-expansion of $g_i$, and, as functions on the upper half-plane, $f \mid_k W = \sum_i \iota(c_i)\, g_i$, with $\mid_k$ Mathlib's weight-$k$ slash action for $\mathrm{GL}_2(\mathbb{R})$.
--
--   This is the Atkin–Lehner analogue, at the exact divisor $Q = M/p$ of $M$, of Shimura's result that the Fricke transform of a form with rational Fourier expansion is a $\overline{\mathbb{Q}}$-linear combination of forms with integral expansions; the condition on $H$ makes the level structure at $p$ of $\Gamma_0(p)$-type, so that $W$ normalises $\Gamma_H(M)$. The proof cites the corresponding Fricke statement together with integrality results for slashing by elements of $\Gamma_0(M)$ and by the Atkin–Lehner matrices, and the theorem is used in the study of the function field of $X_H$ under the Atkin–Lehner cofactor involution and in an integrality statement for $q$-expansions of Atkin–Lehner slashes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_slash_atkinLehnerCofactor_eq_sum_smul_of_ratCast_qExpansion_of_even.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_slash_atkinLehnerCofactor_eq_sum_smul_of_ratCast_qExpansion_of_even
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hxyzw : ((M / p : ℕ) : ℤ) * x * w - (p : ℤ) * y * z = 1)
    (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((M / p : ℕ) : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), ((M / p : ℕ) : ℝ) * (w : ℝ)])
    {k : ℤ} (hk : Even k)
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ)
      (g : Fin n → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      (pg : Fin n → PowerSeries ℤ), (∀ i, ModularCurve.IsIntegralQExp (g i) (pg i)) ∧
        (⇑f : UpperHalfPlane → ℂ) ∣[k] W = ∑ i, ι (c i) • (⇑(g i) : UpperHalfPlane → ℂ) := by sorry
