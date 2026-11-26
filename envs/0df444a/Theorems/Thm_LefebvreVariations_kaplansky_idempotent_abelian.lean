-- Prove2me | Theorems.Thm_LefebvreVariations_kaplansky_idempotent_abelian
-- name    : LefebvreVariations.kaplansky_idempotent_abelian
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:44:10.217109+00:00
-- url     : https://prove2.me/theorems/f068a44c-3c5e-4ac7-b092-f1728bda913f
-- title:
--   Lefebvre's variations, No. 60 — on a theme by Kaplansky: idempotents of the group algebra of a torsion-free abelian group are trivial
-- statement:
--   Let $K$ be a field and $G$ a commutative group that is torsion-free, i.e. every element of finite order equals $1$. Then every idempotent of the group algebra $K[G]$ is trivial:
--   $$
--   \forall a\in K[G],\qquad a^2=a \;\Longrightarrow\; a=0 \ \text{ or } \ a=1 .
--   $$
--
--   This is the abelian case of Kaplansky's idempotent conjecture, which asserts the same for every torsion-free group $G$ and remains open in general (it is implied by the zero-divisor conjecture, since $a^2=a$ means $a(a-1)=0$). For torsion-free abelian $G$ the group algebra is an integral domain, which settles the case.
--
--   **Formalization Note** The statement is `a = 0 ∨ a = 1` for `a : MonoidAlgebra K G` with `ha : IsIdempotentElem a` (that is, `a * a = a`), where `K : Type` is a `[Field K]`, `G : Type` is a `[CommGroup G]`, and `hG : ∀ g : G, IsOfFinOrder g → g = 1`. It is exactly the parent `FCP.Kaplansky.idempotent_conjecture` with `[Group G]` strengthened to `[CommGroup G]`; `hG` is used (it gives the domain property of `K[G]`).
--
--   **Why this is a variation.** Variation on the open FCP.Kaplansky.idempotent_conjecture (idempotents of the group algebra K[G] of a torsion-free group are trivial). It adds the hypothesis that G is commutative, a classical special case that follows from the zero-divisor property of K[G] for abelian torsion-free G.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Origin of this statement: the abelian case of Kaplansky's idempotent conjecture, platform problem FCP.Kaplansky.idempotent_conjecture (Open), with G assumed commutative. The conjecture is attributed to Kaplansky; no page or theorem number is quoted here. The abelian case is an elementary consequence of the definitions together with Mathlib: a torsion-free abelian group has the unique-product property (it embeds in an ordered Q-vector space), so K[G] has no zero divisors, and a^2 = a gives a(a-1) = 0. (Earlier drafts mentioned Passman 1977 ch. 13; that reference was not verified and is deliberately omitted.)

import Mathlib

namespace LefebvreVariations

/-- Kaplansky's idempotent conjecture (`FCP.Kaplansky.idempotent_conjecture`), played at its
classical first case: for a field `K` and a **commutative** torsion-free group `G`, the only
idempotents of `K[G]` are `0` and `1`. Same hypotheses as the parent, plus commutativity of `G`.
Proof idea: `K[G]` is a domain (torsion-free abelian groups are orderable), and in a domain
`a² = a` gives `a (a - 1) = 0`.
Source: classical; the idempotent conjecture is due to Kaplansky (Passman, *The Algebraic Structure
of Group Rings*, 1977, Ch. 13) and follows from the zero-divisor property -- cited from memory. -/
theorem kaplansky_idempotent_abelian (K : Type) [Field K] (G : Type) [CommGroup G]
    (hG : ∀ g : G, IsOfFinOrder g → g = 1) (a : MonoidAlgebra K G) (ha : IsIdempotentElem a) :
    a = 0 ∨ a = 1 := by
  sorry

end LefebvreVariations
