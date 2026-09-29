-- Prove2me | Theorems.Thm_ModularForm_isZeroAt_alSlash
-- name    : ModularForm.isZeroAt_alSlash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/80411c21-3a44-5709-9a0e-969ad9560122
-- title:
--   Vanishing at cusps is preserved under the Atkin–Lehner slash
-- statement:
--   Let $M$ and $q$ be natural numbers with $M \neq 0$, and let $W$ be an Atkin–Lehner datum for the pair $(M,q)$, that is, a natural number $R$ together with a proof that $M = qR$ and integers $a,b$ satisfying the Bézout relation $qa - Rb = 1$. Let $k$ be an integer and let $f : \mathbb{H} \to \mathbb{C}$ be an arbitrary function on the upper half-plane. Assume that for every point $c'$ of the one-point compactification $\mathbb{R} \cup \{\infty\}$ which is a cusp of $\Gamma_0(M)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$, the function $f$ is zero at $c'$ in weight $k$; and let $c$ be a point of $\mathbb{R} \cup \{\infty\}$ which is a cusp of $\Gamma_0(M)$ in the same sense. Then the weight-$k$ slash $f \mid_k W.\mathrm{alGL}$ of $f$ by the element of $\mathrm{GL}_2(\mathbb{R})$ obtained from the integral matrix attached to the datum $W$ (whose determinant is nonzero) is zero at $c$ in weight $k$. Here being zero at a cusp and being a cusp are the Mathlib notions `OnePoint.IsZeroAt` and `IsCusp`.
--
--   This is the statement that the Atkin–Lehner involution $w_q$ preserves vanishing at the cusps: since the matrix of the datum normalises $\Gamma_0(M)$ and hence permutes its cusps, a function vanishing at all cusps of $\Gamma_0(M)$ still does so after slashing. It supplies the cuspidality condition needed to regard $f \mapsto f \mid_k W.\mathrm{alGL}$ as an operator on cusp forms of level $\Gamma_0(M)$, and is used in the results on $q$-expansion coefficients of primitive forms at primes $q$ with $q^2 \nmid M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_isZeroAt_alSlash.lean

import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.isZeroAt_alSlash {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ c' : OnePoint ℝ, IsCusp c' (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) → OnePoint.IsZeroAt c' f k)
    {c : OnePoint ℝ} (hc : IsCusp c (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    OnePoint.IsZeroAt c (ModularForm.alSlash W k f) k := by sorry
