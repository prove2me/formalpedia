-- Prove2me | Theorems.Thm_OAI_Erdos3_uniformBlockSpectrum_tail_s2
-- name    : OAI.Erdos3.uniformBlockSpectrum_tail_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:31:45.773912+00:00
-- url     : https://prove2.me/theorems/8173e048-d699-45ae-b44c-455b763e415b
-- title:
--   The Fourier tail of a product of minor-arc-small block coefficients outside the uniform block spectrum cover is small
-- statement:
--   Let $B$ and $J$ be finite types, $J$ with decidable equality, and let $M, n, t$ be natural numbers. Let `coeff` $: B \to (J \to \operatorname{Fin} M) \to \mathbb{C}$, and let $U, V, W, L, \zeta, \varepsilon$ be reals with $U \ge 1$, $V \ge 0$, $W \ge 0$, $L \ge 0$, $0 < \zeta \le 1$ and $\varepsilon \ge 0$. Assume:
--   - `uniformSpectrumBlockCount n |J| t` $\le |B|$ (an explicit natural number of OpenAI);
--   - $M^{|J|} \le W L^t$;
--   - (hminor) for every $\delta$ with $0 < \delta \le 1$ and $\texttt{majorArcLengthConstant n U} / \delta^{\texttt{majorArcLengthExponent n}} \le L$, every $b \in B$ and every frequency $k : J \to \operatorname{Fin} M$ not in `polynomialGridCover J M (majorArcCoverConstant n |J| U V) (majorArcCoverExponent n |J|) δ`, one has $\lVert \texttt{coeff}(b, k) \rVert \le \delta$ (here `polynomialGridCover J M C r δ` is OpenAI's rational major box with denominator and height parameter $\lceil C / \delta^r \rceil$, and the other constants and exponents are explicit functions of OpenAI);
--   - `uniformBlockSpectrumAccuracyConstant n |J| t U V W` $\cdot \zeta \le \varepsilon$ (an explicit real number of OpenAI).
--
--   Then
--   $$\sum_{k \notin \mathcal{S}} \Bigl\lVert \prod_{b \in B} \texttt{coeff}(b, k) \Bigr\rVert \le \varepsilon,$$
--   where the sum is over all $k : J \to \operatorname{Fin} M$ outside $\mathcal{S}$ = `uniformBlockSpectrumCover J M n U V L ζ` (OpenAI's finite set of frequencies built from the length-aware cover of the polynomial grid cover), i.e. `spectrumTail` of $k \mapsto \lVert \prod_b \texttt{coeff}(b, k) \rVert$.
--
--   Lean: `OAI.Erdos3.uniformBlockSpectrum_tail_s2`, which states OpenAI's `OAI.Erdos3.uniformBlockSpectrum_tail` (in `lean/OAI/Combinatorics/Progressions/Fourier/UniformScaledRetainedCharacters.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B086` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/UniformScaledRetainedCharacters.lean (declaration OAI.Erdos3.uniformBlockSpectrum_tail)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B086

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem uniformBlockSpectrum_tail_s2 {B J : Type*} [Fintype B] [Fintype J] [DecidableEq J]
    (M n t : ℕ) (coeff : B → (J → Fin M) → ℂ) {U V W L ζ ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hB : uniformSpectrumBlockCount n (Fintype.card J) t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (hminor : ∀ δ, 0 < δ → δ ≤ 1 → majorArcLengthConstant n U / δ ^ majorArcLengthExponent n ≤ L →
      ∀ b k, k ∉ polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
        (majorArcCoverExponent n (Fintype.card J)) δ → ‖coeff b k‖ ≤ δ)
    (haccuracy : uniformBlockSpectrumAccuracyConstant n (Fintype.card J) t U V W * ζ ≤ ε) :
    spectrumTail (uniformBlockSpectrumCover J M n U V L ζ) (fun k => ‖∏ b, coeff b k‖) ≤ ε := by
  sorry

end Erdos3

end

end OAI
end
