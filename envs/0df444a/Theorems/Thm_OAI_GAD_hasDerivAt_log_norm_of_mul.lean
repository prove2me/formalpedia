-- Prove2me | Theorems.Thm_OAI_GAD_hasDerivAt_log_norm_of_mul
-- name    : OAI.GAD.hasDerivAt_log_norm_of_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:09:27.101787+00:00
-- url     : https://prove2.me/theorems/adb96695-54cd-4b35-8d88-0eef01d8348a
-- title:
--   Derivative of $\log|z(s)|$ for a complex curve with logarithmic derivative $w$
-- statement:
--   Let $z:\mathbb{R}\to\mathbb{C}$ be a complex-valued function of a real variable, let $t\in\mathbb{R}$ and $w\in\mathbb{C}$. Suppose that $z$ is differentiable at $t$ with derivative $z'(t)=z(t)\,w$, and that $z(t)\neq0$. Then the real function $s\mapsto\log|z(s)|$ (natural logarithm of the modulus) is differentiable at $t$, and
--
--   $$
--   \frac{d}{ds}\Big|_{s=t}\log|z(s)|=\operatorname{Re}w .
--   $$
--
--   In other words $\frac{d}{ds}\log|z|=\operatorname{Re}(z'/z)$, obtained without choosing a branch of the complex logarithm. Applied to $z(s)=\det A(s)$ together with Jacobi's formula $z'(t)=z(t)\operatorname{tr}\bigl(A'(t)A(t)^{-1}\bigr)$, it gives the derivative of $\log|\det A(s)|$ along curves of nonsingular complex matrices whose determinants need not be real.
--
--   **Formalization Note** $|z(s)|$ is the complex norm `‖z s‖` and the logarithm is `Real.log`. The hypothesis is `HasDerivAt z (z t * w) t`, so $w$ plays the role of the logarithmic derivative $z'(t)/z(t)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean#L108-L127

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation

open OAI OAI.GAD
universe u_1 u_2
open scoped BigOperators
open Matrix
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

theorem OAI.GAD.hasDerivAt_log_norm_of_mul {z : ℝ → ℂ} {w : ℂ} {t : ℝ}
    (hz : HasDerivAt z (z t * w) t) (h0 : z t ≠ 0) :
    HasDerivAt (fun s ↦ Real.log ‖z s‖) w.re t := by sorry
