-- Prove2me | Theorems.Thm_OAI_LinearListHadwiger_Recursion_outer_region
-- name    : OAI.LinearListHadwiger.Recursion.outer_region
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:46:32.681086+00:00
-- url     : https://prove2.me/theorems/fb86eb19-0b49-4a8a-b3d0-5640c3b515d5
-- title:
--   Outer region with a role routing and two highly connected regions, or a fractional obstruction (OpenAI, linear list Hadwiger)
-- statement:
--   This is a step of the recursion. There are constants $A \ge 1$ and $T \ge 1$ with the following property. Take natural numbers $a$ and $p$ with $a \ge 1$, $T \le 64a$ and $p \le 3a$. Take a finite graph $G$, injective families of $a$ vertices $r$ and $2p$ vertices $n$ with disjoint ranges. Assume:
--   - $G$ is $30a$-connected (`KConnectedOn G univ (30*a)`);
--   - $h(G) < 64a$;
--   - $\chi_{\mathrm{list}}(G) > Aa$.
--
--   Then one of two things holds. The first is that there are disjoint vertex sets $H$ and $D$ and a set $U$ with three properties:
--   - there is a role routing of $r$ and $n$ through $H$ into $D$ avoiding $U$ (`RoleRouting`);
--   - $H$ and $D$ are both $(K_0\cdot 64a)$-connected;
--   - $\chi_{\mathrm{list}}(G) \le \ell(H) + (4\cdot 32768 + 47 + 6K_0)\cdot 64a$.
--
--   The second is that $G$ has a fractional obstruction. Here $K_0$ = `K₀` is a fixed constant, and the Lean statement gives the exact form of the constant ($4\cdot32768+42+5+6K_0$).
--
--   The named functions come from the definitions bundle `OAIQWLLH000` of this split and the published bundle `Def_ListHadwiger`. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.LinearListHadwiger.Recursion.outer_region`, OpenAI's theorem of that name in `lean/OAI/Combinatorics/ListHadwiger/RecursiveJunction.lean`.
-- source:
--   OpenAI, A linear list-coloring bound in terms of the Hadwiger number, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ListHadwiger/RecursiveJunction.lean (declaration OAI.LinearListHadwiger.Recursion.outer_region)

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQWLLH000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Recursion
open Finset Stage Footprint SmallList Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem outer_region : ∃ A : ℕ, 1≤A ∧ ∃ T : ℕ, 1≤T ∧
    ∀ a : ℕ, 1≤a → T≤64*a → ∀ p : ℕ, p≤3*a →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (r : Fin a → V) (n : Fin (2*p) → V),
    Function.Injective r → Function.Injective n → (∀ i j, r i≠n j) →
    KConnectedOn G univ (30*a) → hadwigerNumber G<64*a →
    A*a<listChromaticNumber G →
    (∃ H D : Finset V, ∃ U : Set V,
      Nonempty (RoleRouting G r n (↑(univ.image r):Set V) (↑H:Set V) D U) ∧
      Disjoint H D ∧ KConnectedOn G H (K₀*(64*a)) ∧
      KConnectedOn G D (K₀*(64*a)) ∧
      listChromaticNumber G≤ell G H+(4*32768+42+5+6*K₀)*(64*a)) ∨
      FractionalObstruction G := by
  sorry

end LinearListHadwiger.Recursion

end OAI
end
