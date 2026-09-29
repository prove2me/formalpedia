-- Prove2me | Theorems.Thm_ModularForm_isBoundedAt_alSlash
-- name    : ModularForm.isBoundedAt_alSlash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/ab2f849a-1eaa-525d-abeb-6abb8540b33a
-- title:
--   Boundedness at cusps is preserved by f ↦ f∣_k W_q
-- statement:
--   Fix natural numbers $M$ and $q$ with $M \neq 0$, and let $W$ be an Atkin–Lehner datum for the pair $(M,q)$, that is: a natural number $R$ together with the factorisation $M = qR$ and integers $a, b$ satisfying the Bézout relation $qa - Rb = 1$. Let $k$ be an integer and $f : \mathbb{H} \to \mathbb{C}$ a function on the upper half-plane. Assume that $f$ is bounded in weight $k$ at every cusp of $\Gamma_0(M)$, the latter regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$: for every point $c'$ of $\mathbb{P}^1(\mathbb{R}) =$ `OnePoint ℝ` which is a cusp for that subgroup, `OnePoint.IsBoundedAt c' f k` holds. Let $c$ be a point of $\mathbb{P}^1(\mathbb{R})$ which is likewise a cusp of $\Gamma_0(M)$. The conclusion is that the slashed function $\mathrm{alSlash}\,W\,k\,f = f \mid_k W.\mathrm{alGL}$ is bounded in weight $k$ at $c$, where $W.\mathrm{alGL}$ is the element of $\mathrm{GL}_2(\mathbb{R})$ obtained from the integral Atkin–Lehner matrix attached to the datum (of determinant $q$) by entrywise inclusion $\mathbb{Z} \hookrightarrow \mathbb{R}$.
--
--   This is the cusp-boundedness clause needed to see that the Atkin–Lehner involution $w_q$ acts on weight-$k$ modular forms for $\Gamma_0(M)$: since $W.\mathrm{alGL}$ has rational entries it permutes $\mathbb{P}^1(\mathbb{Q})$, so boundedness of $f\mid_k W$ at $c$ reduces to boundedness of $f$ at the cusp $W c$. It serves as one of the conditions verified when the bundled Atkin–Lehner operator on $M_k(\Gamma_0(M))$ is constructed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_isBoundedAt_alSlash.lean

import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.isBoundedAt_alSlash {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ c' : OnePoint ℝ, IsCusp c' (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) → OnePoint.IsBoundedAt c' f k)
    {c : OnePoint ℝ} (hc : IsCusp c (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    OnePoint.IsBoundedAt c (ModularForm.alSlash W k f) k := by sorry
