-- Prove2me | Theorems.Thm_JechSetTheory_silver
-- name    : JechSetTheory.silver
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T02:34:29.752567+00:00
-- url     : https://prove2.me/theorems/5e6cebaa-fd32-4d03-969b-5d09d4078a53
-- title:
--   Jech, Theorem 8.12 (Silver) — GCH below a singular $\kappa$ of uncountable cofinality implies GCH at $\kappa$
-- statement:
--   **Theorem (Silver; Jech 8.12).** Let $\kappa$ be a singular cardinal with $\operatorname{cf}\kappa > \omega$. If $2^{\alpha} = \alpha^{+}$ for every infinite cardinal $\alpha < \kappa$, then
--
--   $$2^{\kappa} \;=\; \kappa^{+}.$$
--
--   In words: the Generalized Continuum Hypothesis cannot fail for the first time at a singular cardinal of uncountable cofinality. This is in sharp contrast with the regular case, where Easton's theorem makes the function $\kappa \mapsto 2^\kappa$ essentially arbitrary (subject only to monotonicity and König's inequality), and it was the first indication that singular cardinal arithmetic obeys theorems of ZFC rather than only consistency results. The restriction to uncountable cofinality is necessary: Magidor showed it is consistent, relative to large cardinals, that GCH holds below $\aleph_\omega$ while $2^{\aleph_\omega} > \aleph_{\omega+1}$.
--
--   **Formalization Note** "Singular" is Mathlib's `IsSingular` ($\aleph_0 \le \kappa$ and $\operatorname{cf}\kappa \neq \kappa$), $\kappa^{+}$ is the cardinal successor, and the GCH hypothesis is stated for infinite $\alpha$ only. That restriction is not a weakening but a necessity: $2^{n} = n^{+}$ already fails for the finite cardinal $n = 2$, so a hypothesis quantified over all cardinals below $\kappa$ would be unsatisfiable and the theorem vacuous.
-- source:
--   Thomas Jech, Set Theory, The Third Millennium Edition, revised and expanded, Springer Monographs in Mathematics, Springer 2003, ISBN 3-540-44085-2, Chapter 8, p. 96, Theorem 8.12 (Silver)

import Mathlib
import Definitions.Def_JechStationary

open Cardinal Order Set JechSetTheory

namespace JechSetTheory

theorem silver (k : Cardinal) (hk : k.IsSingular) (hcf : ℵ₀ < k.ord.cof)
    (hgch : ∀ l : Cardinal, ℵ₀ ≤ l → l < k → 2 ^ l = Order.succ l) :
    2 ^ k = Order.succ k := by sorry

end JechSetTheory
