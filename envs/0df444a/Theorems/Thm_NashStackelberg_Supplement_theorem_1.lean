-- Prove2me | Theorems.Thm_NashStackelberg_Supplement_theorem_1
-- name    : NashStackelberg.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:33:24.805013+00:00
-- url     : https://prove2.me/theorems/985f763e-a938-456b-b092-d404d1e6bbdd
-- title:
--   Theorem 1 — deciding whether a trivial NASP has a pure Nash equilibrium is $\Sigma_2^p$-hard
-- statement:
--   A **trivial NASP** (Definition 8) is a simultaneous game between two leaders, each of whom has a single follower solving a linear program $\min_y (c_f+Hw)^\top y$ s.t. $Aw+By\le b$ parameterized by the leader's variables $w$. Leader $i$ chooses $x^i=(w^i,y^i)$ in its feasible region $\mathcal F^i=\{x^i\in\mathcal S^i: y^i\in\mathrm{SOL}(P(w^i))\}$ (optimistic convention) and minimizes $(c^i)^\top x^i+(C^ix^{-i})^\top x^i$. A **pure Nash equilibrium (PNE)** is a profile $(x^1,x^2)$ with $x^i\in\mathcal F^i$ from which no leader can lower its cost by a unilateral change within $\mathcal F^i$.
--
--   **Theorem 1.** It is $\Sigma_2^p$-hard to decide whether a trivial NASP with rational data has a PNE:
--   $$
--   L'\ \le_p\ \textsf{PNE-TRIVIAL-NASP}\qquad\text{for every language } L'\in\Sigma_2^p .
--   $$
--
--   The theorem places the existence of pure equilibria in NASPs at the second level of the polynomial hierarchy, even with two players, one follower per leader and linear followers.
--
--   **Formalization Note** $\Sigma_2^p$, its hardness and polynomial-time many-one reductions are the published `BudgetCoreExchange.Sigma2Hard` (Cook's one-tape Turing machines). $\textsf{PNE-TRIVIAL-NASP}$ is the set of binary codes of rational trivial NASPs that have a PNE (published `IsPNE` on `NASP.F`, `NASP.cost`).
--
--   Differences from the source:
--   - encoding: "decide if a trivial NASP has a PNE/MNE" (no input encoding fixed) → the language of binary codes (RatInstance.encode, published encNat/encQ) of rational trivial NASPs; strings that are not codes are excluded; reason: a decision problem needs a finite input; rational data in binary is the standard encoding, and any other standard binary encoding is polynomial-time equivalent
--   - encoding: Σ₂ᵖ-hard → BudgetCoreExchange.Sigma2Hard: every Σ₂ᵖ language over every finite nonempty alphabet reduces by a polynomial-time many-one reduction (Cook's one-tape machines); reason: the standard definition of Σ₂ᵖ-hardness
--   - encoding: trivial NASP (Definition 8) → RatInstance.toNASP: the published NASP 2 with followers' game K = 1, Q = 0, the unused follower coupling set to 0 and the unused diagonal cost blocks C i i coded; reason: the omitted or fixed entries never enter 𝓕ⁱ or the costs, so every rational trivial NASP is the game of some code
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Theorem 1, p.8; Definition 8, p.30; Definitions 2 and 4, pp.7–8; Remark 2, p.8

import Mathlib
import Definitions.Def_BudgetCoreExchange_Sigma2P
import Definitions.Def_NashStackelberg_Supplement_Languages

namespace NashStackelberg.Supplement

/-- **Theorem 1: deciding whether a trivial NASP has a PNE is Σ₂ᵖ-hard** (Carvalho, Dragotto,
Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, Theorem 1,
p.8: "It is Σ₂ᵖ-hard to decide if a trivial NASP has a PNE").

Every language in Σ₂ᵖ, over every finite nonempty alphabet, reduces by a polynomial-time
many-one reduction (Cook's one-tape machines) to the language `PNELang` of binary codes of
rational trivial NASPs (Definition 8, p.30) that have a pure Nash equilibrium.

**Formalization Note.** Σ₂ᵖ-hardness is the published `BudgetCoreExchange.Sigma2Hard`. A PNE is
the published `IsPNE` on the players' feasible regions `𝓕ⁱ` (optimistic convention) and costs
`(cⁱ)ᵀxⁱ + (Cⁱx⁻ⁱ)ᵀxⁱ`. Instances are coded in binary (`RatInstance.encode`). -/
theorem theorem_1 : BudgetCoreExchange.Sigma2Hard PNELang := by sorry

end NashStackelberg.Supplement
