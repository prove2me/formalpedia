-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_nodal_seed_normalized_trace
-- name    : HodgeComputer.FourPlusTwoResidual.nodal_seed_normalized_trace
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-24T07:29:35.31108+00:00
-- url     : https://prove2.me/theorems/6f57aa7b-2ed7-43b8-8b7c-122e6c63b6e9
-- title:
--   Three-sheet companion-matrix adjugate clearing and normalized trace at the coupled nodal contact
-- statement:
--   At the coupled nodal branch $r = 0$ where $1 + \alpha^3 B = 0$ and $x = \alpha^2$ satisfies $x^3 = 1/B^2$:
--
--   1. In the cubic companion representation $X = \operatorname{seedMulX}(k)$, the adjugate matrix $\operatorname{adj} = \operatorname{seedAdjugateNumerator}(k, u, v)$ satisfies $(u I + v X) \operatorname{adj} = (u^3 + k v^3) I$, and the intrinsic top source simplifies via $a^3 B = -1$ to $3 a^4 B C (2 C B' - 3 B C')$.
--
--   2. Over any characteristic-zero field with $B \neq 0$ and $B^2 u^3 + v^3 \neq 0$, the normalized traces of $(X^3, X^2, X)(u I + v X)^{-1}$ equal
--
--   $$
--   \left(\frac{u^2}{B^2 u^3 + v^3},\; -\frac{u v}{B^2 u^3 + v^3},\; \frac{v^2}{B^2 u^3 + v^3}\right).
--   $$
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` and GitHub Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

theorem HodgeComputer.FourPlusTwoResidual.nodal_seed_normalized_trace :
    (∀ {K : Type} [CommRing K] (k u v : K),
      ((u • (1 : Matrix (Fin 3) (Fin 3) K) + v • HodgeComputer.FourPlusTwoResidual.seedMulX k) *
          HodgeComputer.FourPlusTwoResidual.seedAdjugateNumerator k u v =
        (u ^ 3 + k * v ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K)) ∧
      (∀ (a B C B' C' : K), a ^ 3 * B = -1 →
        let beta := -C * a ^ 2
        let g := C ^ 3 - B ^ 2
        let g' := 3 * C ^ 2 * C' - 2 * B * B'
        let Er := -(3 * a ^ 2 * B)
        let EZ := a ^ 3 * B'
        let EY := Er * (-C' * a ^ 2) + (-(2 * C * a)) * EZ
        a * (3 * g * beta * EY - beta ^ 2 * Er * g') - 6 * g * beta ^ 2 * EZ =
          3 * a ^ 4 * B * C * (2 * C * B' - 3 * B * C'))) ∧
    (∀ {F : Type} [Field F] [CharZero F] (B u v : F),
      B ≠ 0 → B ^ 2 * u ^ 3 + v ^ 3 ≠ 0 →
      let k := 1 / B ^ 2
      let d := 3 * (u ^ 3 + k * v ^ 3)
      let X := HodgeComputer.FourPlusTwoResidual.seedMulX k
      let adj := HodgeComputer.FourPlusTwoResidual.seedAdjugateNumerator k u v
      ((X ^ 3 * adj).trace / d, (X ^ 2 * adj).trace / d, (X * adj).trace / d) =
        (u ^ 2 / (B ^ 2 * u ^ 3 + v ^ 3),
          -(u * v) / (B ^ 2 * u ^ 3 + v ^ 3),
          v ^ 2 / (B ^ 2 * u ^ 3 + v ^ 3))) := by sorry
