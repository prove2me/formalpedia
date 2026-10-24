-- Prove2me | Theorems.Thm_OAI_Problem315_SliceNormalized_reindexed_projection_energy_le_swap_sum
-- name    : OAI.Problem315.SliceNormalized.reindexed_projection_energy_le_swap_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:13:42.473858+00:00
-- url     : https://prove2.me/theorems/fe4ac76f-4f83-4086-bfcb-8e204e9a8eda
-- title:
--   Equality-indicator projections on a subset slice are bounded by the transposition energy
-- statement:
--   **Setting.** Let $V$ be a finite set with $N$ elements, $q \le N$, and let the slice $X_{N,q}$ be the set of $q$-element subsets of $V$ (`SliceEuclideanGenerator.State V q`). Let $\Omega$ be a finite type with a bijection $e : \Omega \to X_{N,q}$, and use on functions $f : \Omega \to \mathbb R$ the Euclidean inner product $\langle f, g \rangle = \sum_{\omega} f(\omega)\,g(\omega)$.
--
--   For $i, j \in V$:
--   - $z_{ij}$ = `SliceNormalized.reindexedRaw e i j` is $0$ if $i = j$, and otherwise the function $\omega \mapsto \mathbf 1[i \in e(\omega) \leftrightarrow j \in e(\omega)] - p$, where $p = \frac{q(q-1) + (N-q)(N-q-1)}{N(N-1)}$ is the probability that $i$ and $j$ are both in or both out of a uniform $q$-subset;
--   - $Q_{ij}$ is the orthogonal projection onto the line spanned by $z_{ij}$ (zero when $z_{ij} = 0$);
--   - $\tau_{ij}$ exchanges $i$ and $j$ in the subset: $\omega \mapsto e^{-1}(\mathrm{swap}_{ij}(e(\omega)))$, written with `SliceEuclideanGenerator.swapState q i j`.
--
--   **Statement.** For every $f : \Omega \to \mathbb R$,
--   $$\frac12 \sum_{i, j \in V} \|Q_{ij} f\|^2 \le \frac18 \sum_{i, j \in V} \sum_{\omega \in \Omega} \bigl(f(\omega) - f(\tau_{ij}\omega)\bigr)^2,$$
--   both sums over ordered pairs $(i, j)$. Since the diagonal terms vanish and $\|(I-\tau_{ij})f/2\|^2 = \frac14 \sum_\omega (f(\omega) - f(\tau_{ij}\omega))^2$, this says $\sum_{i<j} Q_{ij} \preceq \frac12 \sum_{i<j} (I - \tau_{ij})$.
--
--   This is Lemma 6.1 (Equality-indicator projections on a slice) of the paper (OpenAI, *Polynomial mixing of the switch chain for every graphical degree sequence*), "$S := \sum_{i<j} Q_{ij} \preceq G$" with $G = \frac12 \sum_{i<j} (I - \tau_{ij})$ on the uniform slice $X_{N,q}$, stated here for any finite type in bijection with the slice. The paper's inner product is the uniform average, which differs from the one here by the factor $\binom Nq$ on both sides.
--
--   Lean: `OAI.Problem315.SliceNormalized.reindexed_projection_energy_le_swap_sum`, OpenAI's theorem of that name. The definitions come from the definitions bundle `OAIQWSWC002` of this split (with the bundles it imports).
-- source:
--   OpenAI, Polynomial mixing of the switch chain for every graphical degree sequence, OpenAI Math Release, September 25, 2026, Lemma 6.1, https://github.com/openai/math (result family 131; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SwitchChain/SliceReindexedComparison.lean (declaration OAI.Problem315.SliceNormalized.reindexed_projection_energy_le_swap_sum)

import Mathlib
import Definitions.Def_OAIQWSWC002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized

variable {V Ω : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V] [sectionFintypeΩ : Fintype Ω]

 theorem reindexed_projection_energy_le_swap_sum {q : ℕ}
    (e : Ω ≃ State V q) (hq : q ≤ Fintype.card V) (f : EuclideanSpace ℝ Ω) :
    (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ reindexedRaw e i j).starProjection f‖ ^ 2 ≤
      (1/8 : ℝ) * ∑ i, ∑ j, ∑ ω : Ω,
        (f ω - f (e.symm (SliceEuclideanGenerator.swapState q i j (e ω)))) ^ 2 := by
  sorry

end Problem315.SliceNormalized

end

end OAI
end
