-- Prove2me | Theorems.Thm_OAI_CubeShuffle_UnitaryFinite_full_palindrome_decay
-- name    : OAI.CubeShuffle.UnitaryFinite.full_palindrome_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T20:56:07.078776+00:00
-- url     : https://prove2.me/theorems/c1aa1050-bdd2-4dbb-b3b8-75b9062850dd
-- title:
--   In a high-dimensional irreducible unitary representation, the averaged butterfly palindrome has norm at most D^(-1/8000) (OpenAI Thorp sweep)
-- statement:
--   An intermediate statement of the split of OpenAI's proof of the weighted sweep moment theorem (`OAI.CubeShuffle.WeightedSweep.weighted_sweep_moments`, the paper's Theorem 1.1): the spectral bound for the butterfly palindrome in the regime where the dimension is at least exponential in the number of cards with a large constant.
--
--   **Notation** (published bundle `Def_WeightedSweepMoments` and definitions bundle `OAIQWCSH000` of this split). The $2^d$ card positions are `Card d` $= \{0,1\}^d$. For coin vectors $X, Y$ indexed by the switches of the $d$-level butterfly network, `palindromePerm d (X, Y)` is $B(X)\,B(Y)^{-1}$, where $B(X)$ is the permutation of `Card d` that the butterfly network with switch settings $X$ performs (`butterflyPerm`, `decodeButterfly`). For a representation $\rho$ of a group $G$ and a map $P$ from a finite coin space $\Omega$ to $G$, `sampleOperator ρ P` is the average $|\Omega|^{-1}\sum_{\omega}\rho(P(\omega))$ over uniformly random coins. For a Young diagram $\mu$, `space μ` is its Specht module (the span of the polytabloids), `hilbertSpace μ` its realization as a Hilbert space, and for a bijection $e$ from `Card d` to the cells of $\mu$, `relabelledUnitary μ e` is the unitary Specht representation of $\mu$ read as a representation of the permutations of `Card d`.
--
--   **The statement.** Let $\rho$ be an irreducible unitary representation of the permutations of `Card d` on a finite-dimensional complex inner product space of dimension $D > 0$, with
--   $$K\,2^d \le \frac{\log D}{4000} \quad\text{and}\quad 8000 \log 2 \le \log D,$$
--   where $K$ is the absolute constant `DimensionEstimates.densityConstant`. Then the averaged palindrome operator satisfies
--   $$\Bigl\|\ \mathbb E_{X,Y}\,\rho\bigl(B(X)B(Y)^{-1}\bigr)\Bigr\| \le \exp\Bigl(-\frac{\log D}{8000}\Bigr) = D^{-1/8000}.$$
-- source:
--   OpenAI, Row–column symmetry and contraction of coordinate sweeps, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CubeShuffle/NetworkSpectral.lean (declaration OAI.CubeShuffle.UnitaryFinite.full_palindrome_decay)

import Mathlib
import Definitions.Def_WeightedSweepMoments
import Definitions.Def_OAIQWCSH000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical
open DimensionEstimates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem full_palindrome_decay (d : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V)
    (hden : densityConstant*(2:ℝ)^d≤Real.log (Module.finrank ℂ V)/4000)
    (hl : 8000*Real.log 2≤Real.log (Module.finrank ℂ V)) :
    ‖sampleOperator ρ (palindromePerm d)‖≤Real.exp (-Real.log (Module.finrank ℂ V)/8000) := by
  sorry

end CubeShuffle.UnitaryFinite

end OAI
end
