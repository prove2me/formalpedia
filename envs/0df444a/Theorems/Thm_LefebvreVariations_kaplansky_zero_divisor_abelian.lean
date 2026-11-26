-- Prove2me | Theorems.Thm_LefebvreVariations_kaplansky_zero_divisor_abelian
-- name    : LefebvreVariations.kaplansky_zero_divisor_abelian
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:37:51.358798+00:00
-- url     : https://prove2.me/theorems/6d9b0d2d-8089-5970-8bc6-00719a1c2fc8
-- title:
--   Lefebvre's variations, No. 40 — on a theme by Kaplansky: zero-divisor conjecture for torsion-free abelian groups
-- statement:
--   Let $K$ be a field and $G$ a commutative group that is torsion-free, i.e. every element $g\in G$ of finite order equals $1$. Then the group algebra $K[G]$ has no zero divisors:
--   $$
--   \forall a,b\in K[G],\qquad ab=0 \;\Longrightarrow\; a=0 \ \text{ or } \ b=0 .
--   $$
--   In other words, $K[G]$ is an integral domain (it is commutative here, and nonzero because $K$ is).
--
--   This is the abelian case of Kaplansky's zero-divisor conjecture, which asserts the same conclusion for every torsion-free group $G$, abelian or not, and remains open in general. The abelian case is the first non-trivial instance: a torsion-free abelian group can be ordered, which gives it the unique-product property and hence the absence of zero divisors in $K[G]$.
--
--   **Formalization Note** The statement is `NoZeroDivisors (MonoidAlgebra K G)` for `K : Type` with `[Field K]` and `G : Type` with `[CommGroup G]`, under the hypothesis `hG : ∀ g : G, IsOfFinOrder g → g = 1`. It is exactly the parent `FCP.Kaplansky.zero_divisor_conjecture` with `[Group G]` strengthened to `[CommGroup G]`; `hG` is the parent's own torsion-freeness hypothesis and is used. `NoZeroDivisors` says `a * b = 0 → a = 0 ∨ b = 0`; there is no hypothesis on the size of `G` (the trivial group is allowed).
--
--   **Why this is a variation.** This varies Kaplansky's zero-divisor conjecture, which says that the group algebra $K[G]$ of a torsion-free group $G$ over a field has no zero divisors. It is the special case of commutative groups, the classical first case, where torsion-free abelian groups are orderable. It settles the parent for all abelian $G$ and leaves the non-commutative groups as the open part.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Origin of this statement: the abelian case of Kaplansky's zero-divisor conjecture, platform problem FCP.Kaplansky.zero_divisor_conjecture (Open), with G assumed commutative. The conjecture is attributed to Kaplansky; no page or theorem number is quoted here. The abelian case is an elementary consequence of the definitions together with Mathlib: a torsion-free abelian group A embeds in the Q-vector space Q (x) A, which is ordered, so A has the unique-sums property (Mathlib: UniqueSums.of_injective_addHom), and Mathlib proves that unique products over a domain give NoZeroDivisors for the monoid algebra. (Earlier drafts mentioned Passman 1977 ch. 13, Levi 1913 and Higman 1940; those references were not verified and are deliberately omitted.)

import Mathlib

namespace LefebvreVariations

/-- Kaplansky's zero-divisor conjecture (`FCP.Kaplansky.zero_divisor_conjecture`), played at its
classical first case: for a field `K` and a **commutative** torsion-free group `G`, the group
algebra `K[G]` has no zero divisors. The hypothesis `hG` is the parent's own torsion-freeness
hypothesis. Proof idea: a torsion-free abelian group embeds in a `ℚ`-vector space, which is
ordered, hence has the unique-product property.
Source: the conjecture is attributed to Kaplansky (it is stated e.g. in Passman, *The Algebraic
Structure of Group Rings*, Wiley 1977, Ch. 13); the abelian case is classical (torsion-free abelian
groups are orderable, Levi 1913; Higman, *The units of group-rings*, Proc. LMS 1940, treats
unique-product groups) -- attributions cited from memory, not verified. -/
theorem kaplansky_zero_divisor_abelian (K : Type) [Field K] (G : Type) [CommGroup G]
    (hG : ∀ g : G, IsOfFinOrder g → g = 1) : NoZeroDivisors (MonoidAlgebra K G) := by
  sorry

end LefebvreVariations
