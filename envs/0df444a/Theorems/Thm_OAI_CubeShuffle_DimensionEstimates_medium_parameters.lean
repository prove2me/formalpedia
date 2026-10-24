-- Prove2me | Theorems.Thm_OAI_CubeShuffle_DimensionEstimates_medium_parameters
-- name    : OAI.CubeShuffle.DimensionEstimates.medium_parameters
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T20:55:59.363558+00:00
-- url     : https://prove2.me/theorems/6ea95bec-7b7c-4df4-83a3-2621dcfaae7b
-- title:
--   Medium-dimension parameters: the modified palindrome row moment is at most exp((h/4000)·2^(L+r)) (OpenAI Thorp sweep)
-- statement:
--   An intermediate statement of the split of OpenAI's proof of the weighted sweep moment theorem (`OAI.CubeShuffle.WeightedSweep.weighted_sweep_moments`, the paper's Theorem 1.1): the parameter choice for the medium-dimension regime of the palindrome spectral bound.
--
--   **Notation** (published bundle `Def_WeightedSweepMoments` and definitions bundle `OAIQWCSH000` of this split). The $2^d$ card positions are `Card d` $= \{0,1\}^d$. For coin vectors $X, Y$ indexed by the switches of the $d$-level butterfly network, `palindromePerm d (X, Y)` is $B(X)\,B(Y)^{-1}$, where $B(X)$ is the permutation of `Card d` that the butterfly network with switch settings $X$ performs (`butterflyPerm`, `decodeButterfly`). For a representation $\rho$ of a group $G$ and a map $P$ from a finite coin space $\Omega$ to $G$, `sampleOperator ρ P` is the average $|\Omega|^{-1}\sum_{\omega}\rho(P(\omega))$ over uniformly random coins. For a Young diagram $\mu$, `space μ` is its Specht module (the span of the polytabloids), `hilbertSpace μ` its realization as a Hilbert space, and for a bijection $e$ from `Card d` to the cells of $\mu$, `relabelledUnitary μ e` is the unitary Specht representation of $\mu$ read as a representation of the permutations of `Card d`.
--
--   **Further notation.** Split the $L + r$ butterfly levels into $r$ outer levels and central blocks of $2^L$ cards indexed by `Card r`. For a set $E$ of central blocks, `modifiedPerm L r E` is OpenAI's modified palindrome on $2^{L+r}$ cards: a random output butterfly $B(Y)$ composed with the inverse of an input routing tree whose outer levels use fresh coins $X$ and whose central map in block $u$ is a uniformly random permutation $U_u$ of `Card L` when $u \notin E$ and is the output butterfly's own central map when $u \in E$ (so the central permutation of an exceptional block is the identity; `ModifiedRouting.modifiedBoundary`, `modifiedInputTree`). For an injective tuple $e$ of positions and $a \ge 0$, `modifiedRowMoment L r E e a` is the average over target tuples $f$ of $\bigl(N \cdot \Pr[\text{the modified palindrome sends } e \text{ to } f]\bigr)^{1+a}$, where $N$ is the number of target tuples (`PairRouting.tupleProbability`, `finiteMean`).
--
--   **The statement.** For every $h > 0$ there are $L > 0$, $0 < \varepsilon < 1/2$ and $t \ge 0$ with
--   $$t\varepsilon + \log(1 + e^{-t}) \le h\,2^L/16000$$
--   such that, for all sufficiently large $r$, every set $E$ of fewer than $\varepsilon 2^r$ blocks and every full tuple $e$ (an injection of `Card (L+r)` into itself),
--   $$\text{modifiedRowMoment}(L, r, E, e, 1/1000) \le \exp\bigl((h/4000)\,2^{L+r}\bigr).$$
-- source:
--   OpenAI, Row–column symmetry and contraction of coordinate sweeps, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CubeShuffle/DimensionEstimates.lean (declaration OAI.CubeShuffle.DimensionEstimates.medium_parameters)

import Mathlib
import Definitions.Def_WeightedSweepMoments
import Definitions.Def_OAIQWCSH000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CubeShuffle.DimensionEstimates
open scoped BigOperators Classical
open Filter

lemma medium_parameters (h : ℝ) (hh : 0<h) :
    ∃ L : ℕ, 0<L ∧ ∃ ε t : ℝ, 0<ε ∧ ε<1/2 ∧ 0≤t ∧
      t*ε+Real.log (1+Real.exp (-t))≤h*(2:ℝ)^L/16000 ∧
      ∀ᶠ r : ℕ in atTop, ∀ (E : Finset (Card r)), (E.card:ℝ)<ε*(2:ℝ)^r →
        ∀ e : Card (L+r) ↪ Card (L+r),
          modifiedRowMoment L r E e (1/1000)≤Real.exp ((h/4000)*(2:ℝ)^(L+r)) := by
  sorry

end CubeShuffle.DimensionEstimates

end OAI
end
