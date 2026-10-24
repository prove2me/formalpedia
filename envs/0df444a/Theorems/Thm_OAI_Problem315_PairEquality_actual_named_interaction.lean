-- Prove2me | Theorems.Thm_OAI_Problem315_PairEquality_actual_named_interaction
-- name    : OAI.Problem315.PairEquality.actual_named_interaction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:12:31.973897+00:00
-- url     : https://prove2.me/theorems/3c2939fc-b9a3-49fe-8c31-0632efd1497d
-- title:
--   Disjoint-pair interaction bound for pair resamplings
-- statement:
--   **Setting.** Fix $n$ and a degree sequence $d$, let $\Omega_d$ be the set of simple graphs on $\{0, \dots, n-1\}$ with degree $d(v)$ at every vertex (`GraphState n d`, published bundle `Def_SwitchChain`), and let `PairResampling.StateSpace n d` be the Euclidean space of real functions on $\Omega_d$, $\langle f, g \rangle = \sum_G f(G)\,g(G)$. For a vertex pair $a$, $h_a$ = `PairResampling.fluctuation n d a` is $I - E_a$, where $E_a$ is conditional expectation on the $a$-fibers (graphs agreeing off $a$, inside $a$, and in each outside vertex's number of neighbours in $a$).
--
--   Let $i, j, k, l$ be four distinct vertices (`FourDistinct i j k l`), $a = \{i, j\}$ and $b = \{k, l\}$.
--   - $T_{a,b}$ toggles the four edges between $a$ and $b$ when exactly one of the matchings $\{ik, jl\}$, $\{il, jk\}$ is present (the 2-by-2 cross matrix is a permutation matrix), and fixes the graph otherwise. In Lean it is the flip of the switch proposal `CrossToggle.crossProposal i j k l h`, which exchanges $\{ik, lj\}$ and $\{il, kj\}$, and `SwitchFlip.projection` of it is $g_{a,b} = (I - T_{a,b})/2$.
--   - On an $a$-fiber in which both $k$ and $l$ have exactly one neighbour in $a$, let $z_{kl}$ be the indicator that $k$ and $l$ are adjacent to the same endpoint of $a$ (in Lean, $ik \in G \leftrightarrow il \in G$) minus its average over the fiber; on other fibers put $z_{kl} = 0$. `PairEquality.projection i j k l` is $R_{a,b}$, the orthogonal projection onto the functions that on each $a$-fiber are a multiple of $z_{kl}$. `PairEquality.projection k l i j` is $R_{b,a}$, the same with the roles of the two pairs exchanged.
--
--   **Statement.** For every function $f$ on $\Omega_d$,
--   $$2\,\|g_{a,b} f\|^2 - \|R_{a,b} f\|^2 - \|R_{b,a} f\|^2 \le 2\,\langle h_a f, h_b f \rangle.$$
--
--   This is Proposition 5.1 (Disjoint-pair interaction) of the paper (OpenAI, *Polynomial mixing of the switch chain for every graphical degree sequence*): "For disjoint vertex pairs $a, b$ and every real function $f$ on $\Omega_d$, $2\langle h_a f, h_b f\rangle \ge 2\|g_{a,b} f\|^2 - \|R_{a,b} f\|^2 - \|R_{b,a} f\|^2$." The Lean inner product is the paper's $E_{\pi_d}$ inner product multiplied by $|\Omega_d|$, which scales both sides alike.
--
--   Lean: `OAI.Problem315.PairEquality.actual_named_interaction`, OpenAI's theorem of that name. The definitions come from the definitions bundle `OAIQWSWC000` of this split and the published bundle `Def_SwitchChain`.
-- source:
--   OpenAI, Polynomial mixing of the switch chain for every graphical degree sequence, OpenAI Math Release, September 25, 2026, Proposition 5.1, https://github.com/openai/math (result family 131; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SwitchChain/PairActualAffine.lean (declaration OAI.Problem315.PairEquality.actual_named_interaction)

import Mathlib
import Definitions.Def_SwitchChain
import Definitions.Def_OAIQWSWC000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling DisjointEncoding DisjointMarginal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem actual_named_interaction (i j k l : Fin n) (h : FourDistinct i j k l)
    (f : StateSpace n d) :
    2 * ‖SwitchFlip.projection (CrossToggle.crossProposal i j k l h) f‖ ^ 2 -
        ‖projection i j k l f‖ ^ 2 - ‖projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫ := by
  sorry

end Problem315.PairEquality

end

end OAI
end
