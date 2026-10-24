-- Prove2me | Theorems.Thm_OAI_Problem315_PairResampling_spectralGap_of_triples_and_disjoint
-- name    : OAI.Problem315.PairResampling.spectralGap_of_triples_and_disjoint
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:14:19.504012+00:00
-- url     : https://prove2.me/theorems/0b71640b-b2e0-4e31-888b-cca6f761aad1
-- title:
--   Spectral gap of the switch chain from the triple and disjoint-pair estimates
-- statement:
--   **Setting.** Let $\Omega_d$ be the set of simple graphs on $\{0, \dots, n-1\}$ with degree $d(v)$ at every vertex (`GraphState n d`, published bundle `Def_SwitchChain`), and `PairResampling.StateSpace n d` the Euclidean space of real functions on $\Omega_d$, $\langle f, g \rangle = \sum_G f(G)\,g(G)$. For a vertex pair $a$, $h_a$ = `PairResampling.fluctuation n d a` is $I - E_a$, with $E_a$ conditional expectation on the $a$-fibers (graphs agreeing off $a$, inside $a$, and in each outside vertex's number of neighbours in $a$). For a vertex set $T$, $H_T$ = `PairResampling.tripleGenerator n d T` is $\sum_{a \subseteq T,\ |a|=2} h_a$, and `PairResampling.pairs n` is the set of all vertex pairs.
--
--   The conclusion is about the switch chain of the published goal: `hasSpectralGapAtLeast n d γ` (bundle `Def_SwitchChain`) says that for every real function $f$ on $\Omega_d$, $\gamma \operatorname{Var}(f) \le \mathcal E(f)$, where the variance is under the uniform law on $\Omega_d$ and $\mathcal E(f)$ is the uniform average of $f \cdot (f - Pf)$ for the lazy switch kernel $P$ (`switchKernel`: holding probability $1/2$, and each of the $6\binom n4$ proposals of a four-vertex set with an ordered pair of distinct perfect matchings on it has weight $1/(12\binom n4)$).
--
--   **Statement.** Let $n \ge 4$ and let $d$ be graphical ($\Omega_d$ is nonempty). Assume
--   1. for every $f$ and every three-element vertex set $T$, $\langle f, H_T f\rangle \le \langle H_T f, H_T f\rangle$ (that is, $H_T^2 \succeq H_T$);
--   2. for every $f$, $\displaystyle 0 \le \sum_{a,b \text{ disjoint pairs}} \langle h_a f, h_b f\rangle$, the sum over ordered pairs $(a, b)$ of disjoint vertex pairs.
--
--   Then `hasSpectralGapAtLeast n d (1 / (24 n² C(n,4)))`: the switch chain has spectral gap at least $1/(24 n^2 \binom n4)$.
--
--   This packages Section 7 of the paper (OpenAI, *Polynomial mixing of the switch chain for every graphical degree sequence*). The two assumptions are the paper's Proposition 4.1 and Corollary 6.3. From them Proposition 7.1 gives $H^2 \succeq H$ for $H = \sum_a h_a$. Lemma 7.2 ("Any two graphs in $\Omega_d$ can be joined by a sequence of valid switches") and Corollary 7.3 identify the kernel of $H$ and give $\operatorname{Var}(f) \le \langle f, Hf\rangle$. The comparison $H \preceq 2n^2 L$ with the switch Laplacian (Lemma 7.4) and $I - P_d = L/(12\binom n4)$ then give the gap $\gamma_0 = 1/(24n^2\binom n4)$ of equation (7.8).
--
--   Lean: `OAI.Problem315.PairResampling.spectralGap_of_triples_and_disjoint`, OpenAI's theorem of that name. The definitions come from the definitions bundle `OAIQWSWC002` of this split (with the bundles it imports) and the published bundle `Def_SwitchChain`.
-- source:
--   OpenAI, Polynomial mixing of the switch chain for every graphical degree sequence, OpenAI Math Release, September 25, 2026, Section 7 (Proposition 7.1, Lemma 7.2, Corollary 7.3, Lemma 7.4 and equation (7.8)), https://github.com/openai/math (result family 131; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SwitchChain/LocalGapEndgame.lean (declaration OAI.Problem315.PairResampling.spectralGap_of_triples_and_disjoint)

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

theorem spectralGap_of_triples_and_disjoint
    {n : Nat} {d : Fin n → Nat} (hn : 4 ≤ n) (hgraph : Graphical n d)
    (htriple : ∀ (f : StateSpace n d) (T : Finset (Fin n)), T.card = 3 →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (hdisjoint : ∀ f : StateSpace n d,
      0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
        if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  sorry

end Problem315.PairResampling

end

end OAI
end
