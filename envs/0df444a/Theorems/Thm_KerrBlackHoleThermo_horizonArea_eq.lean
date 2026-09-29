-- Prove2me | Theorems.Thm_KerrBlackHoleThermo_horizonArea_eq
-- name    : KerrBlackHoleThermo.horizonArea_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T19:44:56.709578+00:00
-- url     : https://prove2.me/theorems/316fadf0-5dd4-4cb3-a691-c3b2142543d3
-- title:
--   Kerr horizon area: $A = 8\pi M\,(M+\sqrt{M^2-a^2})$
-- statement:
--   Let $M>0$ and $a$ be real numbers with $a^2\le M^2$. Let $A(M,a)$ be the area of the event horizon of the Kerr black hole of mass $M$ and rotation parameter $a$, i.e. the area of the 2-surface $t=\text{const}$, $r=r_+=M+\sqrt{M^2-a^2}$ computed from the induced Boyer–Lindquist metric $g_{\theta\theta}\,d\theta^2+g_{\varphi\varphi}\,d\varphi^2$:
--   $$A(M,a)=\int_0^{\pi}\!\!\int_0^{2\pi}\sqrt{g_{\theta\theta}(r_+,\theta)\,g_{\varphi\varphi}(r_+,\theta)}\;d\varphi\,d\theta.$$
--   Then
--   $$A(M,a) = 8\pi M\left(M+\sqrt{M^2-a^2}\right).$$
--
--   This is eq. (3.44) of the dissertation, the closed form of the horizon area used in the first law.
--
--   **Formalization Note** The dissertation obtains (3.44) by combining the Smarr relation (3.43) with (2.42) and (3.3); here the area is defined directly from the metric (see the definition file), so the statement is an independent check of the closed form.
-- source:
--   F. H. de C. Menezes, Termodinâmica de Buracos Negros, M.Sc. dissertation, Programa de Pós-Graduação em Física, ICEx, Universidade Federal de Minas Gerais, Belo Horizonte, 2021 (advisor: N. de O. Yokomizo), Section 3.2.3, eq. (3.44), p. 66

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

open Real

namespace KerrBlackHoleThermo

/-- Milestone, eq. (3.44): the area of the Kerr event horizon is
`A = 8 π M (M + √(M² − a²))`. -/
theorem horizonArea_eq (M a : ℝ) (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
    horizonArea M a = 8 * π * M * (M + √(M ^ 2 - a ^ 2)) := by
  sorry

end KerrBlackHoleThermo
