-- Prove2me | Theorems.Thm_NashStackelberg_Supplement_theorem_2
-- name    : NashStackelberg.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:35:45.824623+00:00
-- url     : https://prove2.me/theorems/ef29b553-fbaa-54fc-9703-a94049ae158b
-- title:
--   Theorem 2 — deciding whether a trivial NASP has a mixed Nash equilibrium is $\Sigma_2^p$-hard
-- statement:
--   A **trivial NASP** (Definition 8) is a simultaneous game between two leaders, each of whom has a single follower solving a linear program $\min_y (c_f+Hw)^\top y$ s.t. $Aw+By\le b$ parameterized by the leader's variables $w$. Leader $i$ chooses $x^i=(w^i,y^i)$ in its feasible region $\mathcal F^i=\{x^i\in\mathcal S^i: y^i\in\mathrm{SOL}(P(w^i))\}$ (optimistic convention) and minimizes $f^i(x^i,x^{-i})=(c^i)^\top x^i+(C^ix^{-i})^\top x^i$. A **mixed Nash equilibrium (MNE)** (Definition 2) is a pair of independent probability distributions $\sigma^i$ on $\mathcal F^i$ such that, for each $i$ and each $\tilde x^i\in\mathcal F^i$,
--   $$
--   \mathbb E_{X\sim\sigma}\big[f^i(X^i,X^{-i})\big]\le\mathbb E_{X^{-i}\sim\sigma^{-i}}\big[f^i(\tilde x^i,X^{-i})\big].
--   $$
--
--   **Theorem 2.** It is $\Sigma_2^p$-hard to decide whether a trivial NASP with rational data has an MNE:
--   $$
--   L'\ \le_p\ \textsf{MNE-TRIVIAL-NASP}\qquad\text{for every language } L'\in\Sigma_2^p .
--   $$
--
--   The feasible regions of a trivial NASP may be unbounded. When they are bounded an MNE always exists (Corollary 1), so the difficulty lies in the unbounded case.
--
--   **Formalization Note** $\Sigma_2^p$-hardness is the published `BudgetCoreExchange.Sigma2Hard` (Cook's one-tape Turing machines, polynomial-time many-one reductions). $\textsf{MNE-TRIVIAL-NASP}$ is the set of binary codes of rational trivial NASPs that have an MNE in the sense of the published `IsMNE`: Borel probability measures concentrated on the $\mathcal F^i$, with integrable costs, and no finite-support restriction.
--
--   Differences from the source:
--   - encoding: "decide if a trivial NASP has a PNE/MNE" (no input encoding fixed) → the language of binary codes (RatInstance.encode, published encNat/encQ) of rational trivial NASPs; strings that are not codes are excluded; reason: a decision problem needs a finite input; rational data in binary is the standard encoding, and any other standard binary encoding is polynomial-time equivalent
--   - encoding: Σ₂ᵖ-hard → BudgetCoreExchange.Sigma2Hard: every Σ₂ᵖ language over every finite nonempty alphabet reduces by a polynomial-time many-one reduction (Cook's one-tape machines); reason: the standard definition of Σ₂ᵖ-hardness
--   - encoding: trivial NASP (Definition 8) → RatInstance.toNASP: the published NASP 2 with followers' game K = 1, Q = 0, the unused follower coupling set to 0 and the unused diagonal cost blocks C i i coded; reason: the omitted or fixed entries never enter 𝓕ⁱ or the costs, so every rational trivial NASP is the game of some code
--   - encoding: MNE of Definition 2 (expectations over mixed strategies) → published IsMNE: independent Borel probability measures concentrated on the 𝓕ⁱ, with integrable costs and deviation costs; reason: Definition 2 compares expectations, which must exist; no finite-support restriction is imposed (that restriction belongs to Algorithm 1 only)
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Theorem 2, p.8; proof EC §9.2, pp.31–32; Definition 8, p.30; Definitions 2 and 4, pp.7–8; Remark 2, p.8

import Mathlib
import Definitions.Def_BudgetCoreExchange_Sigma2P
import Definitions.Def_NashStackelberg_Supplement_Languages

namespace NashStackelberg.Supplement

/-- **Theorem 2: deciding whether a trivial NASP has an MNE is Σ₂ᵖ-hard** (Carvalho, Dragotto,
Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, Theorem 2,
p.8: "It is Σ₂ᵖ-hard to decide if a trivial NASP has an MNE"; proof in EC §9, pp.30–32).

Every language in Σ₂ᵖ, over every finite nonempty alphabet, reduces by a polynomial-time
many-one reduction (Cook's one-tape machines) to the language `MNELang` of binary codes of
rational trivial NASPs (Definition 8, p.30) that have a mixed Nash equilibrium.

**Formalization Note.** Σ₂ᵖ-hardness is the published `BudgetCoreExchange.Sigma2Hard`. An MNE
is the published `IsMNE` (Definition 2): independent Borel probability measures concentrated on
the feasible regions `𝓕ⁱ` (optimistic convention), with integrable costs and no profitable pure
deviation in expectation; no finite-support restriction. Instances are coded in binary
(`RatInstance.encode`); their feasible regions may be unbounded. -/
theorem theorem_2 : BudgetCoreExchange.Sigma2Hard MNELang := by sorry

end NashStackelberg.Supplement
