-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_cyclicProjection_double_apply
-- name    : OAI.CirculantHadamard.cyclicProjection_double_apply
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:15:53.573872+00:00
-- url     : https://prove2.me/theorems/09d6a350-e59d-4025-8c13-fce9e89ce40f
-- title:
--   Coefficients of the projection from Z/2m to Z/m
-- statement:
--   Write $R[\mathbb Z/n]$ for the cyclic group ring (finitely supported coefficient functions on $\mathbb Z/n$ with convolution), $e_a$ for its basis element at $a$, and $f^{*}(a)=\overline{f(-a)}$ for its involution, which reverses indices and applies the coefficient star. Let $m>0$ and let $\pi:R[\mathbb Z/2m]\to R[\mathbb Z/m]$ reduce indices modulo $m$. For $f\in R[\mathbb Z/2m]$ and $j\in\mathbb Z/m$ with representative $\bar j\in\{0,\dots,m-1\}$,
--   $$
--   \pi(f)(j)=f(\bar j)+f(\bar j+m).
--   $$
--
--   Each coefficient of the projection is the sum of the two coefficients of $f$ lying over it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/ProjectionCoefficients.lean#L65-L82

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection

open OAI OAI.CirculantHadamard
universe uA uB uR
open scoped BigOperators
variable {R : Type uR} [Semiring R]

theorem OAI.CirculantHadamard.cyclicProjection_double_apply {m : ℕ} (hm : 0 < m) (h : m ∣ 2 * m)
    (f : CyclicRing.Elem R (2 * m)) (j : ZMod m) :
    (cyclicProjection R h f).coeff j =
      f.coeff (j.val : ZMod (2 * m)) + f.coeff ((j.val + m : ℕ) : ZMod (2 * m)) := by sorry
