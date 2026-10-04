-- Prove2me | Theorems.Thm_HJMEilenberg_syntactic_universal
-- name    : HJMEilenberg.syntactic_universal
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-09T10:36:12.085817+00:00
-- url     : https://prove2.me/theorems/a3fa8fba-0854-4b76-a7df-3c1f858eede1
-- title:
--   Syntactic congruence universal property
-- statement:
--   Let $A$ be a many-sorted $\Sigma$-algebra and $L$ a sorted language in $A$. The syntactic congruence $\Omega_A(L)$ saturates $L$, and for every congruence $\Phi$ on $A$,
--
--   $$
--   \text{$\Phi$ saturates $L$}\quad\Longleftrightarrow\quad \Phi\le \Omega_A(L).
--   $$
--
--   Thus $\Omega_A(L)$ is exactly the greatest algebra congruence whose equivalence classes preserve membership in $L$. This universal property connects the supremum-style Lean definition with the syntactic congruence used throughout the paper.
-- source:
--   Juan Climent Vidal and Enric Cosme Llópez, Eilenberg theorems for many-sorted formations, Houston Journal of Mathematics 45(2) (2019), Section 6, pp. 351–416; arXiv:1604.04792. The free-term substrate is cross-checked against the companion TeX source A Kleene theorem for free many-sorted algebras. Section 5, Proposition CharacCogenCong and Proposition CharacSatCCog.

import Definitions.Def_HJMEilenberg_Formations

namespace HJMEilenberg

open MSKleene

/-- Proposition 5.4: the syntactic congruence is the greatest congruence
saturating a language. -/
theorem syntactic_universal {S : Type} {sig : Signature S}
    (A : Algebra sig) (L : Language A) :
    Saturated (syntacticCongruence A L) L ∧
      ∀ Phi : Congruence A,
        Saturated Phi L ↔ Phi ≤ syntacticCongruence A L := by
  sorry

end HJMEilenberg
