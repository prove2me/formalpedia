-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetWhittaker3_mul_eq_modulus_det_cpow_mul_jacquetWhittaker3
-- name    : LanglandsTunnell.CubicInduction.jacquetWhittaker3_mul_eq_modulus_det_cpow_mul_jacquetWhittaker3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/25284425-423c-5372-9eb7-076f7d0df88f
-- title:
--   Modulus twist of the GL₃ Jacquet–Whittaker function
-- statement:
--   Let $v$ be a point of the height-one spectrum of $\mathcal O_{\mathbb Q}$, so that $\mathbb Q_v$ denotes the corresponding adic completion of $\mathbb Q$. Let $\chi = (\chi_0,\chi_1,\chi_2)$ be a triple of group homomorphisms $\mathbb Q_v^\times \to \mathbb C^\times$, let $\Phi : \mathbb Q_v^3 \to \mathbb C$ be an arbitrary function, let $\mu : \mathbb Q_v^\times \to \mathbb C^\times$ be a group homomorphism and $a \in \mathbb R$, and assume that $\mu(u) = \mathrm{modulus}(u)^a$ for every unit $u$, where $\mathrm{modulus}(x)$ is the module of multiplication by $x$ on a Haar measure of $\mathbb Q_v$ (set to $0$ at $x = 0$), the power being the complex power with exponent $a$. Then for every $g \in GL_3(\mathbb Q_v)$ the Jacquet–Whittaker function attached to the componentwise twisted triple $(\chi_i\mu)_i$ and to $\Phi$ satisfies $$W_{\chi\mu,\Phi}(g) = \mathrm{modulus}(\det g)^a\, W_{\chi,\Phi}(g).$$ Here $W_{\chi,\Phi}(g)$ is the stabilised truncated Jacquet integral `jacquetValue` of the right translate by $g$ of the cell section of $(\chi,\Phi)$, namely of the function supported on the big cell `bigCell3` given there by $h \mapsto \mathrm{cellValue}(\chi,h)\,\Phi(\mathrm{cellRatio}(h))$. No continuity, smoothness or integrability hypothesis on $\chi$, $\mu$ or $\Phi$ is imposed.
--
--   This is the elementary equivariance of the Jacquet–Whittaker construction on $GL_3$ under twisting the inducing quasi-characters by a power of the local absolute value: such a twist multiplies the Whittaker function by the corresponding power of $|\det|_v$. It is used in the construction of a determinant twist of a Jacquet–Whittaker function with prescribed central behaviour and gauge bounds.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetWhittaker3_mul_eq_modulus_det_cpow_mul_jacquetWhittaker3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.jacquetWhittaker3_mul_eq_modulus_det_cpow_mul_jacquetWhittaker3
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (μ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℝ)
    (hμ : ∀ u : (v.adicCompletion ℚ)ˣ,
      ((μ u : ℂˣ) : ℂ) = ((modulus (u : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (a : ℂ))
    (g : LocalGL3 v) :
    jacquetWhittaker3 v (fun i => χ i * μ) Φ g =
      ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (a : ℂ) *
        jacquetWhittaker3 v χ Φ g := by sorry
