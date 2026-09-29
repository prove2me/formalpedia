-- Prove2me | Theorems.Thm_ModularForm_isZeroAt_add_heckeU_alSlash
-- name    : ModularForm.isZeroAt_add_heckeU_alSlash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/774108c3-53d1-55e1-bf02-1ddc43dc55b0
-- title:
--   Vanishing at cusps of f + U_q(f∣_k W_q)
-- statement:
--   Let $M$ and $q$ be natural numbers with $M \neq 0$, and let $W$ be an Atkin–Lehner datum for the pair $(M,q)$: this consists of a natural number $R$ together with a proof that $M = qR$, and integers $a,b$ with $qa - Rb = 1$. Let $k$ be an integer and $f : \mathbb{H} \to \mathbb{C}$ a function on the upper half plane. Assume that for every point $c'$ of $\mathbb{P}^1(\mathbb{R}) =$ `OnePoint ℝ` which is a cusp of $\Gamma_0(M)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$, the function $f$ is zero at $c'$ in weight $k$. Let $c$ be a point of `OnePoint ℝ` which is a cusp of $\Gamma_0(R)$, where $R$ is the component `W.R` of the datum. The conclusion is that the function
--   $$f + \sum_{j=0}^{q-1} \bigl(f \mid_k W.\mathrm{alGL}\bigr) \mid_k \begin{pmatrix} 1 & j \\ 0 & q\end{pmatrix}$$
--   is zero at $c$ in weight $k$; here $W.\mathrm{alGL}$ is the element of $\mathrm{GL}_2(\mathbb{R})$ obtained from the integral matrix attached to the datum (invertible since $q > 0$), the slash is the weight-$k$ action, and for $q = 0$ the matrices in the sum are replaced by the identity, the sum then being empty.
--
--   This is the cusp-vanishing half of the construction of the Atkin–Lehner trace map from level $M = qR$ to level $R$: the combination $f + U_q(f \mid_k W_q)$ is the natural candidate for a form of level $R$, and the statement records that it vanishes at all cusps of $\Gamma_0(R)$ as soon as $f$ vanishes at all cusps of $\Gamma_0(M)$. It supplies the cusp condition needed when the trace of a cusp form is bundled as a cusp form of the lower level, in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_isZeroAt_add_heckeU_alSlash.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.isZeroAt_add_heckeU_alSlash {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ c' : OnePoint ℝ, IsCusp c' (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) → OnePoint.IsZeroAt c' f k)
    {c : OnePoint ℝ} (hc : IsCusp c (CongruenceSubgroup.Gamma0 W.R : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    OnePoint.IsZeroAt c (f + ModularForm.heckeU k q (ModularForm.alSlash W k f)) k := by sorry
