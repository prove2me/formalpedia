-- Prove2me | Theorems.Thm_OAI_CubeShuffle_Specht_near_row_amplification
-- name    : OAI.CubeShuffle.Specht.near_row_amplification
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T20:56:06.572989+00:00
-- url     : https://prove2.me/theorems/92451608-6949-474c-b622-2b1b9e11c2a4
-- title:
--   Near-row amplification: the averaged palindrome on a Specht module is bounded through the dimension of a tuple-fixed subspace (OpenAI Thorp sweep)
-- statement:
--   An intermediate statement of the split of OpenAI's proof of the weighted sweep moment theorem (`OAI.CubeShuffle.WeightedSweep.weighted_sweep_moments`, the paper's Theorem 1.1): the amplification bound used for diagrams whose first row is long.
--
--   **Notation** (published bundle `Def_WeightedSweepMoments` and definitions bundle `OAIQWCSH000` of this split). The $2^d$ card positions are `Card d` $= \{0,1\}^d$. For coin vectors $X, Y$ indexed by the switches of the $d$-level butterfly network, `palindromePerm d (X, Y)` is $B(X)\,B(Y)^{-1}$, where $B(X)$ is the permutation of `Card d` that the butterfly network with switch settings $X$ performs (`butterflyPerm`, `decodeButterfly`). For a representation $\rho$ of a group $G$ and a map $P$ from a finite coin space $\Omega$ to $G$, `sampleOperator ρ P` is the average $|\Omega|^{-1}\sum_{\omega}\rho(P(\omega))$ over uniformly random coins. For a Young diagram $\mu$, `space μ` is its Specht module (the span of the polytabloids), `hilbertSpace μ` its realization as a Hilbert space, and for a bijection $e$ from `Card d` to the cells of $\mu$, `relabelledUnitary μ e` is the unitary Specht representation of $\mu$ read as a representation of the permutations of `Card d`.
--
--   **Further notation.** For a $k$-tuple $f$ of distinct positions, `fixedSpace tupleAction f ρ` is the subspace of vectors fixed by every permutation that fixes each position of $f$.
--
--   **The statement.** Let $\mu$ be a Young diagram, $e$ a bijection from `Card d` to the cells of $\mu$, and $f$ a $k$-tuple of distinct positions with $k > 0$, and let $m > 0$ be the dimension of the subspace of the Specht module (`relabelledUnitary μ e`) fixed by the pointwise stabilizer of $f$. Then the averaged palindrome operator $A$ = `sampleOperator (relabelledUnitary μ e) (palindromePerm d)` satisfies
--   $$\|A\| \le \exp\Bigl(K\,k\,\bigl(k/2^d\bigr)^{1/512}\Bigr)\,\bigl(m^{1/2}\bigr)^{-1/1000} + \sqrt{m^{1/2}/m},$$
--   with $K$ = `DimensionEstimates.densityConstant`. (The Lean writes $m^{1/2}$ as $\exp(\log m / 2)$.)
-- source:
--   OpenAI, Row–column symmetry and contraction of coordinate sweeps, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CubeShuffle/ShapeSpectral.lean (declaration OAI.CubeShuffle.Specht.near_row_amplification)

import Mathlib
import Definitions.Def_WeightedSweepMoments
import Definitions.Def_OAIQWCSH000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CubeShuffle.Specht
open scoped BigOperators Classical
open UnitaryFinite DimensionEstimates Filter

lemma near_row_amplification (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ)
    {k : ℕ} (f : Fin k ↪ Card d) (hk : 0<k)
    (hm : 0<Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e))) :
    ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ ≤
      Real.exp (densityConstant*(k:ℝ)*((k:ℝ)/(2:ℝ)^d)^(1/512:ℝ))*
        (Real.exp (Real.log (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)))/2))^(-(1/1000:ℝ))+
      Real.sqrt ((Real.exp (Real.log (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)))/2))/
        (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)):ℝ)) := by
  sorry

end CubeShuffle.Specht

end OAI
end
