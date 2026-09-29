-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero
-- name    : ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/1ac5043c-5fe9-587c-bce9-7fad89018d93
-- title:
--   Modular polynomial at a transcendental j splits over Vélu quotients
-- statement:
--   Let $K_0$ be an algebraically closed field of characteristic zero, let $N \ge 1$, and let `data` be a `ModularPolynomialData N`, that is a polynomial $\Phi \in \mathbb{Z}[X][Y]$ that is monic, of degree $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$ in $Y$, and satisfies $\Phi = 0$ when its integer coefficients are mapped by the ring homomorphism sending $X$ to the $q$-expansion $j(q)$ and $Y$ is set to $j(q^N)$ (`jqN N`), inside Laurent series over $\mathbb{Q}$. Let $W$ be an elliptic Weierstrass curve over $K_0$ whose $j$-invariant is transcendental over $\mathbb{Q}$, let $\iota$ be a finite index type of cardinality $\psi(N)$, and let $Q : \iota \to W(K_0)$ be a family of affine points each of exact additive order $N$ whose generated cyclic subgroups $\langle Q_i\rangle$ are pairwise distinct. Assume further that for every $i$ the curve `W.fullKernelQuotient (Q i) N` — the Vélu-type curve with the same $a_1, a_2, a_3$ and with $a_4$ replaced by $a_4 - 5t$ and $a_6$ by $a_6 - b_2 t - 7w$, where $t = \sum g_x(P)$ and $w = \sum (x_P g_x(P) - y_P g_y(P))$, the sums running over the coordinates of $k \cdot Q_i$ for $1 \le k \le N-1$, with $g_x = 3x^2 + 2a_2x + a_4 - a_1y$ and $g_y = -(2y + a_1x + a_3)$ — has nonvanishing discriminant. Then the polynomial in $K_0[Y]$ obtained from $\Phi$ by applying to each coefficient the evaluation $\mathbb{Z}[X] \to K_0$ at $j(W)$ equals $\prod_{i} \bigl(Y - j(\mathrm{W.fullKernelQuotient}\ (Q\ i)\ N)\bigr)$, each quotient being elliptic by the discriminant hypothesis.
--
--   This is the classical factorisation of the modular polynomial $\Phi_N(j(W), Y)$ into linear factors indexed by the $\psi(N)$ cyclic $N$-isogenous quotients of $W$, here in the generic case of a transcendental $j$-invariant in characteristic zero and with the quotients realised by Vélu's formulae for the full kernel $\langle Q_i \rangle$. It is used in the construction of $j$-invariant models and of Frobenius-semilinear torsion data on the modular curve, being cited by [`ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j`](thm.html#ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j), [`ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ`](thm.html#ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ) and [`ModularCurve.exists_frobeniusSemilinear_torsionModel_ofJ_univ`](thm.html#ModularCurve.exists_frobeniusSemilinear_torsionModel_ofJ_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_WeierstrassCurve_FullKernelQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open Polynomial ModularCurve WeierstrassCurve WeierstrassCurve.Affine

theorem ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero
    {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
    {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
    {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
    (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K₀ _
      (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by sorry
