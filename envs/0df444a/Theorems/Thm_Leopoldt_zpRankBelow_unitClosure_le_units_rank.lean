-- Prove2me | Theorems.Thm_Leopoldt_zpRankBelow_unitClosure_le_units_rank
-- name    : Leopoldt.zpRankBelow_unitClosure_le_units_rank
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:20:22.865036+00:00
-- url     : https://prove2.me/theorems/13c6b20d-a3f6-49ae-8580-186b68a6a414
-- title:
--   $\mathbb{Z}_p\text{-rk}(\overline{E}) \le \mathbb{Z}\text{-rk}(E)$: the Leopoldt defect is non-negative
-- statement:
--   Let $p$ be a prime and $K$ a number field with unit group $E = \mathcal{O}_K^\times$ and Dirichlet unit rank $r = r_1 + r_2 - 1 = \mathbb{Z}\text{-rk}(E)$. Let $U = \prod_{\wp \mid p} \mathcal{O}_{K_\wp}^\times$ be the semilocal units at $p$, $\iota : E \to U$ the diagonal embedding, and
--   $$\overline{E} = \bigcap_{n \ge 1} \iota(E)\, U^{p^{n}}$$
--   the $p$-adic closure of the global units. Then the $\mathbb{Z}_p$-rank of $\overline{E}$ never exceeds the $\mathbb{Z}$-rank of $E$:
--   $$\mathbb{Z}_p\text{-rk}(\overline{E}) \;\le\; \mathbb{Z}\text{-rk}(E) = r_1 + r_2 - 1 .$$
--
--   Equivalently, the Leopoldt defect $\mathcal{D}_L(K) = \mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\overline{E})$ is a genuine non-negative integer: the truncated subtraction in the mission's definition of `defect` is never triggered. Leopoldt's conjecture asserts that equality holds.
--
--   **Formalization Note** The $\mathbb{Z}_p$-rank is `zpRankBelow p (finrank ℚ K) (unitClosure p K)`, the largest $n \le [K:\mathbb{Q}]$ such that $\mathbb{Z}_p^n$ admits a continuous injective homomorphism into $U$ with image in $\overline{E}$ (from `Definitions.Def_LeopoldtDefect`); Dirichlet's unit rank is Mathlib's `NumberField.Units.rank K`.
-- source:
--   P. Mihăilescu, On CM $\mathbb{Z}_p$-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1 (Notations and fundamental facts): definition of the Leopoldt defect $\mathcal{D}_L(K) = \mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\overline{E})$ as a non-negative integer (Leopoldt's conjecture: $\mathcal{D}_L(K)=0$).

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem zpRankBelow_unitClosure_le_units_rank (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] :
    zpRankBelow p (Module.finrank ℚ K) (unitClosure p K) ≤ Units.rank K := by sorry
end Leopoldt
