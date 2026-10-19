-- Prove2me | Theorems.Thm_OAI_Erdos3_uniformBlockSpectrumCover_polynomial_card_s2
-- name    : OAI.Erdos3.uniformBlockSpectrumCover_polynomial_card_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:34:14.563159+00:00
-- url     : https://prove2.me/theorems/cf53aefa-2e3c-4563-8600-2e0d64fed6ce
-- title:
--   Polynomial bound on the size of the uniform block spectrum cover at the retained bias
-- statement:
--   Let $J$ be a finite type with decidable equality and $M, n, t$ natural numbers. Let $U, V, W, L, \varepsilon$ be real numbers with $U \ge 1$, $V \ge 0$, $W \ge 0$, $L \ge 0$, $0 < \varepsilon \le 1$, and $M^{|J|} \le W L^{t}$. Let
--   $$\zeta = \texttt{uniformBlockRetainedBias}\ n\ |J|\ t\ U\ V\ W\ \varepsilon = \min\Bigl(1,\ \frac{\varepsilon}{\texttt{uniformBlockSpectrumAccuracyConstant}\ n\ |J|\ t\ U\ V\ W + 1}\Bigr),$$
--   and let `uniformBlockSpectrumCover J M n U V L ζ` be the finite set of functions $J \to \mathrm{Fin}\ M$ defined by OpenAI (a length-aware cover of a polynomial grid cover, built from OpenAI's major-arc constants and exponents). Then the number of elements of this cover satisfies
--   $$\bigl|\texttt{uniformBlockSpectrumCover}\ J\ M\ n\ U\ V\ L\ \zeta\bigr| \le \frac{\texttt{uniformSpectrumSizeConstant}\ n\ |J|\ t\ U\ V\ W}{\varepsilon^{\max(\texttt{majorArcSpectrumExponent}\ n\ |J|,\ \texttt{majorArcLengthExponent}\ n\cdot t)}},$$
--   where `uniformSpectrumSizeConstant`, `majorArcSpectrumExponent` and `majorArcLengthExponent` are explicit functions defined by OpenAI.
--
--   Lean: `OAI.Erdos3.uniformBlockSpectrumCover_polynomial_card_s2`, which states OpenAI's `OAI.Erdos3.uniformBlockSpectrumCover_polynomial_card` (in `lean/OAI/Combinatorics/Progressions/Fourier/UniformSpectrumSize.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B086` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/UniformSpectrumSize.lean (declaration OAI.Erdos3.uniformBlockSpectrumCover_polynomial_card)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B086

section

namespace OAI

section

namespace Erdos3

theorem uniformBlockSpectrumCover_polynomial_card_s2 (J : Type*) [Fintype J] [DecidableEq J]
    (M n t : ℕ) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ((uniformBlockSpectrumCover J M n U V L
      (uniformBlockRetainedBias n (Fintype.card J) t U V W ε)).card : ℝ) ≤
      uniformSpectrumSizeConstant n (Fintype.card J) t U V W /
        ε ^ max (majorArcSpectrumExponent n (Fintype.card J)) (majorArcLengthExponent n * t) := by
  sorry

end Erdos3

end

end OAI
end
