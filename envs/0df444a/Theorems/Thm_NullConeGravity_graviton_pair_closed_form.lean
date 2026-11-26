-- Prove2me | Theorems.Thm_NullConeGravity_graviton_pair_closed_form
-- name    : NullConeGravity.graviton_pair_closed_form
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T14:12:39.382593+00:00
-- url     : https://prove2.me/theorems/c1b9d971-782b-5980-85f6-5121843c87ef
-- title:
--   Graviton pair amplitude in closed form
-- statement:
--   The connected amplitude for creating and annihilating a graviton pair on a null cone has a finite closed form at every positive Newton coupling.
--
--   Let $s = \mathscr{A}/(4 G_N \hbar) > 0$ be the dimensionless corner area. With the radial-mode variance $(\Delta q_k)^2 = 1/(2sk)$ and the relative annihilation phase $e^{-2ik/s}$, the connected graviton-pair overlap converges absolutely and evaluates to
--
--   $$ \lim_{N\to\infty} 2\sum_{k=1}^{N} (\Delta q_k)^4\, e^{-2ik/s} = \frac{\operatorname{Li}_2\!\left(e^{-2i/s}\right)}{2 s^2}. $$
--
--   Although each variance is of order $G_N$ and the perturbative expansion in $G_N$ diverges logarithmically (see the companion UV-divergence milestone), the resummed amplitude is finite for every $s>0$: the dilogarithm series converges absolutely on the unit circle $|e^{-2i/s}|=1$. This is the explicit check, in Section 4.4 of the source, that summing over intermediate states before expanding yields a finite gravitational amplitude.
--
--   **Formalization Note.** `pairAmplitude s` is the `tsum` of `pairTerm s k`; the theorem asserts both absolute summability of the summand norms and the identification with `dilog (exp (-2i/s)) / (2 s²)`. The real parameter `s` is coerced to `ℂ` in the phase and prefactor.
-- source:
--   V. Chandrasekaran, An algebraic quantization of gravity from the null cone, https://arxiv.org/abs/2611.34924, Section 4.4, Eq. (4.33) (label bfq:radial-pair-correlator)

import Mathlib
import Definitions.Def_NullConeGravity_dilog
import Definitions.Def_NullConeGravity_pairRadialData

namespace NullConeGravity
theorem graviton_pair_closed_form (s : ℝ) (hs : 0 < s) :
    Summable (fun k : ℕ => ‖pairTerm s k‖) ∧
    pairAmplitude s = dilog (Complex.exp (-2 * Complex.I / (s : ℂ))) / (2 * (s : ℂ) ^ 2) := by sorry
end NullConeGravity
