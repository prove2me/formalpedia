-- Prove2me | Theorems.Thm_FractionalCalc_mittagLeffler_two_cos
-- name    : FractionalCalc.mittagLeffler_two_cos
-- status  : Proved
-- author  : @LG
-- created : 2026-11-20T16:44:55.828899+00:00
-- url     : https://prove2.me/theorems/135a4f70-95e0-45f4-b757-9868c6773c96
-- title:
--   Classical limit $E_2(-z^2)=\cos z$ (§5.2)
-- statement:
--   For every real $z$,
--   $$E_2(-z^2)=\cos z.$$
--   This is the classical limit used in §5.2 of the source: at $\alpha=2$ the fractional oscillator solution $x(t)=E_\alpha(-\omega^\alpha t^\alpha)$ (with $x(0)=1$, $x'(0)=0$) reduces to $\cos(\omega t)$, the integer-order harmonic oscillator. It reflects $E_2(-z^2)=\sum_k(-1)^k z^{2k}/(2k)!=\cos z$.
--
--   **Formalization Note** A standalone identity for the one-parameter Mittag-Leffler function at order $2$.
-- source:
--   F. G. Rodrigues & E. C. de Oliveira, Rev. Bras. Ens. Fís. 37(3), 3305 (2015), https://doi.org/10.1590/S1806-11173731842, §5.2, the limit $\alpha=2$ giving $x(t)=\cos\omega t$.

import Mathlib
import Definitions.Def_FractionalCalc_mittagLeffler
open MeasureTheory Set Classical

namespace FractionalCalc
theorem mittagLeffler_two_cos (z : ℝ) : mittagLefflerOne 2 (-(z ^ 2)) = Real.cos z := by sorry
end FractionalCalc
