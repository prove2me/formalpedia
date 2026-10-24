-- Prove2me | Theorems.Thm_OAI_Problem315_PairResampling_tripleGenerator_square
-- name    : OAI.Problem315.PairResampling.tripleGenerator_square
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:13:39.588429+00:00
-- url     : https://prove2.me/theorems/20f0f2a5-ed7c-402b-a533-c1d8897f399e
-- title:
--   Pair resamplings on a vertex triple satisfy H_T² ⪰ H_T
-- statement:
--   **Setting.** Fix $n$ and a degree sequence $d$ on the vertices $\{0, \dots, n-1\}$, and let $\Omega_d$ be the finite set of simple graphs on these vertices with degree $d(v)$ at every vertex $v$ (`GraphState n d`, from the published bundle `Def_SwitchChain`). `PairResampling.StateSpace n d` is the Euclidean space of real functions on $\Omega_d$, with $\langle f, g \rangle = \sum_{G \in \Omega_d} f(G)\,g(G)$.
--
--   For a vertex pair $a = \{i, j\}$, two graphs lie in the same *$a$-fiber* when they have the same edges with neither endpoint in $a$, the same edges inside $a$, and every vertex $w \notin a$ has the same number of neighbours in $a$ in both. `PairResampling.fluctuation n d a` is $h_a = I - E_a$, the orthogonal projection onto the orthogonal complement of the functions constant on every $a$-fiber; $E_a$ is conditional expectation on the $a$-fibers (each fiber carries the uniform measure). For a set $T$ of vertices, `PairResampling.tripleGenerator n d T` is $H_T = \sum_{a \subseteq T,\ |a| = 2} h_a$.
--
--   **Statement.** For every function $f$ on $\Omega_d$ and every three-element vertex set $T$,
--   $$\langle f, H_T f \rangle \le \langle H_T f, H_T f \rangle,$$
--   that is, $H_T^2 \succeq H_T$ in the order of quadratic forms ($H_T$ is self-adjoint). There are no hypotheses on $n$ or $d$.
--
--   This is Proposition 4.1 of the paper (OpenAI, *Polynomial mixing of the switch chain for every graphical degree sequence*): "For every vertex triple $T$, one has $H_T^2 \succeq H_T$." The paper proves it from its three-row variance inequality (Lemma 3.3), whose equivalent conditional-projection form is due to Fu, Qin and Wang.
--
--   Lean: `OAI.Problem315.PairResampling.tripleGenerator_square`, OpenAI's theorem of that name. The definitions come from the definitions bundle `OAIQWSWC002` of this split (with the bundles it imports) and the published bundle `Def_SwitchChain`.
-- source:
--   OpenAI, Polynomial mixing of the switch chain for every graphical degree sequence, OpenAI Math Release, September 25, 2026, Proposition 4.1, https://github.com/openai/math (result family 131; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SwitchChain/ActualTripleSquare.lean (declaration OAI.Problem315.PairResampling.tripleGenerator_square)

import Mathlib
import Definitions.Def_SwitchChain
import Definitions.Def_OAIQWSWC002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem tripleGenerator_square {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d) (T : Finset (Fin n)) (hT : T.card = 3) :
    ⟪f, tripleGenerator n d T f⟫ ≤
      ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫ := by
  sorry

end Problem315.PairResampling

end

end OAI
end
