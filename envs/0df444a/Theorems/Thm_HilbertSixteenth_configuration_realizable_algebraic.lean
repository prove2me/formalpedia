-- Prove2me | Theorems.Thm_HilbertSixteenth_configuration_realizable_algebraic
-- name    : HilbertSixteenth.configuration_realizable_algebraic
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:12:19.421925+00:00
-- url     : https://prove2.me/theorems/27c4cc98-f310-46e8-9b92-5b20111c0354
-- title:
--   Theorem 1(b): realisation by algebraic limit cycles in degree $\le 2(n+r)-1$
-- statement:
--   Let $\mathcal C=\{C_1,\dots,C_n\}$ be a configuration of limit cycles and let $r$ be the number of its primary curves. Then there is a polynomial vector field $V$ of degree
--   $$\deg V\le 2(n+r)-1$$
--   such that every limit cycle of $V$ is algebraic and $V$ realises $\mathcal C$.
--
--   This strengthens Theorem 1(a) by giving an explicit degree and algebraic limit cycles, showing that every configuration is realisable with algebraic limit cycles.
--
--   **Formalization Note** Only the first sentence of Theorem 1(b) is formalized; the additional assertion that the system has a first integral of Darboux type is omitted. For $n=0$ the degree bound is computed with natural-number subtraction and equals $0$.
-- source:
--   J. Llibre, *Sobre el problema 16 de Hilbert*, La Gaceta de la RSME 18 (2015), no. 3, pp. 543–554, §6, Theorem 1(b), first sentence (Llibre–Rodríguez 2004). The second sentence (Darboux first integral) is not formalized.

import Definitions.Def_HilbertSixteenth_Configurations

namespace HilbertSixteenth
theorem configuration_realizable_algebraic (𝒞 : Finset (Set (ℝ × ℝ)))
    (h𝒞 : IsConfiguration 𝒞) :
    ∃ V : PolyField,
      V.degree ≤ 2 * (𝒞.card + {C : Set (ℝ × ℝ) | IsPrimary 𝒞 C}.ncard) - 1 ∧
      (∀ O : Set (ℝ × ℝ), IsLimitCycle V.toField O → IsAlgebraicLimitCycle V O) ∧
      Realizes V 𝒞 := by sorry
end HilbertSixteenth
