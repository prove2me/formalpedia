-- Prove2me | Theorems.Thm_NullConeGravity_graviton_pair_weak_coupling_log
-- name    : NullConeGravity.graviton_pair_weak_coupling_log
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T19:58:03.673324+00:00
-- url     : https://prove2.me/theorems/937642bd-34c3-46c1-9833-a483fab5d93a
-- title:
--   Weak-coupling logarithm of the summed graviton pair amplitude
-- statement:
--   Let $A(s)$ be the full complex radial graviton pair amplitude of Eq. (4.33), for one polarization and one real angular harmonic. Its imaginary part satisfies $\displaystyle\lim_{s\to+\infty}\frac{s^3\operatorname{Im}A(s)}{\log s}=-1$. The radial modes are summed at fixed positive $s$ before taking the weak-coupling limit.
-- source:
--   V. Chandrasekaran, An algebraic quantization of gravity from the null cone, arXiv:2611.34924v1, §4.4, final paragraph after Eq. (4.34), https://arxiv.org/html/2611.34924v1#S4.SS4.p13. The amplitude is the radial series of Eq. (4.33).

import Definitions.Def_NullConeGravity_pairRadialData

namespace NullConeGravity
theorem graviton_pair_weak_coupling_log :
    Filter.Tendsto (fun s : ℝ => s ^ 3 * (pairAmplitude s).im / Real.log s)
      Filter.atTop (nhds (-1 : ℝ)) := by sorry
end NullConeGravity
