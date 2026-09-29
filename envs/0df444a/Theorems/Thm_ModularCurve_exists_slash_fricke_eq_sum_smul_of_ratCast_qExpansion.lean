-- Prove2me | Theorems.Thm_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
-- name    : ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/916bb612-4205-5968-9d15-5029bada8f9a
-- title:
--   Fricke transform of a rational form on Γ_H(M)
-- statement:
--   Fix a positive integer $M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and an integer $k$. Write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of those $\gamma \in \Gamma_0(M)$ whose associated unit $\gamma \mapsto (d \bmod M)$, with inverse given by $a \bmod M$, lies in $H$; it is regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Let $f$ be a modular form of weight $k$ for this group such that for every $n$ the $n$-th coefficient of the $q$-expansion of $f$ with width $1$ at $\infty$ is the image of a rational number. Let $\iota \colon \overline{\mathbb{Q}} \to \mathbb{C}$ be a ring homomorphism from `AlgebraicClosure ℚ`, and let $W \in \mathrm{GL}_2(\mathbb{R})$ have underlying matrix $\begin{pmatrix} 0 & -1 \\ M & 0\end{pmatrix}$. Then there exist a natural number $n$, elements $c_0,\dots,c_{n-1} \in \overline{\mathbb{Q}}$, modular forms $g_0,\dots,g_{n-1}$ of weight $k$ for the same group, and power series $p_0,\dots,p_{n-1} \in \mathbb{Z}[[X]]$ such that each $p_i$ maps, under $\mathbb{Z} \to \mathbb{C}$, to the width-$1$ $q$-expansion of $g_i$, and such that the weight-$k$ slash $f \mid_k W$ equals $\sum_i \iota(c_i) \cdot g_i$ as functions on the upper half-plane.
--
--   This is the rationality statement for the Fricke involution on $X_H(M)$: the Fricke transform of a weight-$k$ form on $\Gamma_H(M)$ with rational Fourier coefficients at $\infty$ lies in the $\overline{\mathbb{Q}}$-span of forms with integral Fourier expansions. It is used in the treatment of Atkin–Lehner and diamond operators on $q$-expansions and in the identification of the Galois action on the function field of $X_H(M)$ after applying the Fricke matrix.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ)
      (g : Fin n → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      (p : Fin n → PowerSeries ℤ), (∀ i, ModularCurve.IsIntegralQExp (g i) (p i)) ∧
        (⇑f : UpperHalfPlane → ℂ) ∣[k] W = ∑ i, ι (c i) • (⇑(g i) : UpperHalfPlane → ℂ) := by sorry
