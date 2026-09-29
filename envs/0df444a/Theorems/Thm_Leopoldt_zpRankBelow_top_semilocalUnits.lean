-- Prove2me | Theorems.Thm_Leopoldt_zpRankBelow_top_semilocalUnits
-- name    : Leopoldt.zpRankBelow_top_semilocalUnits
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:47:52.328644+00:00
-- url     : https://prove2.me/theorems/47d091e3-3e9c-43e1-a9dd-5a872b5aa6ba
-- title:
--   The semilocal unit group $U$ has $\mathbb{Z}_p$-rank $[K:\mathbb{Q}]$
-- statement:
--   Let $p$ be a prime and $K$ a number field. Let
--   $$U=\prod_{\mathfrak p\mid p}\mathcal O_{\mathfrak p}^{\times}$$
--   be the group of semilocal units at $p$, the product over the primes $\mathfrak p$ of $\mathcal O_K$ above $p$ of the unit groups of the completed local rings of integers, with its product (profinite) topology.
--
--   **Theorem.** The free $\mathbb Z_p$-rank of $U$ equals the degree $[K:\mathbb Q]$. In the platform's formulation via `Leopoldt.zpRankBelow` (the largest $n\le[K:\mathbb Q]$ for which there is a continuous injective group homomorphism $\mathbb Z_p^{\,n}\hookrightarrow U$), this says
--   $$\operatorname{rk}_{\mathbb Z_p}(U)=[K:\mathbb Q].$$
--
--   The upper bound $\le [K:\mathbb Q]$ is built into the definition (and is also the proved theorem `Leopoldt.le_finrank_of_continuous_injective_semilocalUnits`); the content is the lower bound, i.e. the existence of a continuous injection $\mathbb Z_p^{[K:\mathbb Q]}\hookrightarrow U$. This is the fact, used in Section 1.1 of Mihăilescu's paper, that the whole semilocal unit group has $\mathbb Z_p$-rank $[K:\mathbb Q]$, so that the Leopoldt defect measures how far the closure $\overline{E}$ of the global units falls short of its expected rank. Classically it follows from $U^{(1)}_{\mathfrak p}\cong \mu\times\mathbb Z_p^{[K_{\mathfrak p}:\mathbb Q_p]}$ and $\sum_{\mathfrak p\mid p}[K_{\mathfrak p}:\mathbb Q_p]=[K:\mathbb Q]$.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1 ("the Z_p-rank of the whole semilocal unit group U is [K:Q]"); J. Neukirch, Algebraic Number Theory, Ch. II, Prop. 5.7 (structure of U^(1) of a p-adic field) and Ch. II, Prop. 8.3/Cor. 8.4 (K ⊗ Q_p = ∏ K_p, ∑ [K_p:Q_p] = [K:Q]).

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem zpRankBelow_top_semilocalUnits (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] :
    zpRankBelow p (Module.finrank ℚ K) (⊤ : Subgroup (SemilocalUnits p K)) =
      Module.finrank ℚ K := by sorry
end Leopoldt
