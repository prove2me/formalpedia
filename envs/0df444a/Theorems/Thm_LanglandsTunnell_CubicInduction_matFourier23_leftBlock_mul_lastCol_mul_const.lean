-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_matFourier23_leftBlock_mul_lastCol_mul_const
-- name    : LanglandsTunnell.CubicInduction.matFourier23_leftBlock_mul_lastCol_mul_const
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/a76e33d5-0485-5adf-b918-0211fdc22228
-- title:
--   Fourier transform of a pure tensor on M_{2× 3}
-- statement:
--   Let $p$ be a nonzero prime of the ring of integers of $\mathbb Q$, write $F$ for the completion $\mathbb Q_p$ at $p$, and let $\eta$ be an additive character of $F$ with values in $\mathbb C$. Let $\varphi_1 : M_2(F) \to \mathbb C$, $\varphi_2 : F \times F \to \mathbb C$ and $c \in \mathbb C$ be arbitrary, and let $X \in M_{2\times 3}(F)$. All integrals are Bochner integrals against the product of two copies of the measure `selfDualHaarAt` at $p$, namely the additive Haar measure giving the local integers mass $1$ rescaled by the $(-\tfrac12\,\mathrm{level}(\psi_p))$-th power of the absolute norm of $p$, the completion carrying its Borel $\sigma$-algebra. Then the transform `matFourier23`, that is the composite of the column transforms `colFourier23` in columns $2$, $1$, $0$ (each sending $\Phi$ to $X \mapsto \int_{F^2} \Phi(\text{$X$ with column $j$ replaced by $u$})\,\eta(u_1X_{0j}+u_2X_{1j})\,du$), applied to the function $Y \mapsto \varphi_1(Y')\,\varphi_2(Y_{02},Y_{12})\,c$, where $Y'$ denotes the left $2\times 2$ block of $Y$, evaluated at $X$, equals $$\bigl(\mathtt{matFourier22}\,\varphi_1\bigr)(X')\cdot\Bigl(\int_{F^2}\varphi_2(u)\,\eta(u_1X_{02}+u_2X_{12})\,du\Bigr)\cdot c,$$ with `matFourier22` the composite of the two $2\times 2$ column transforms `colFourier22` in columns $1$ then $0$. No measurability, integrability or Schwartz–Bruhat hypothesis is imposed on $\varphi_1$, $\varphi_2$.
--
--   This is the multiplicativity of the local Fourier transform on $2\times 3$ matrices with respect to the decomposition of a matrix into its left $2\times 2$ block and its last column: on a pure tensor the iterated column transform factors as the product of the $2\times 2$ matrix transform and the $F^2$ transform. It is used in the Rankin–Selberg local computation to identify the dual datum attached to a pure-tensor Godement section, in [`LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2`](thm.html#LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_iotaGL_eq_sum_and_dual_eq_mul_sum_of_chamber_ed2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_matFourier23_leftBlock_mul_lastCol_mul_const.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction NumberField.StandardAddChar
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.CubicInduction.matFourier23_leftBlock_mul_lastCol_mul_const
    (p : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (p.adicCompletion ℚ) ℂ)
    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (c : ℂ) (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    matFourier23 p η (fun Y : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => φ₁ (Matrix.of fun a b => Y a (Fin.castSucc b)) * φ₂ (Y 0 2, Y 1 2) * c) X =
      matFourier22 p η φ₁ (Matrix.of fun a b => X a (Fin.castSucc b)) *
        (∫ u : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), φ₂ u * η (u.1 * X 0 2 + u.2 * X 1 2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) * c := by sorry
