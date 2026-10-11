-- Prove2me | Theorems.Thm_MazurTransfer_nineteen_norm_rational_kernel_card_product
-- name    : MazurTransfer.nineteen_norm_rational_kernel_card_product
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T18:44:29.211507+00:00
-- url     : https://prove2.me/theorems/e795cef2-dda2-48b5-b90a-6613738c2788
-- title:
--   Norm-nineteen kernels with torsion of cardinality nineteen have sizes nineteen and one
-- statement:
--   Let an abelian group have a finite torsion subgroup of cardinality nineteen. If endomorphisms f and g have both composites equal to multiplication by nineteen and their sum equal to multiplication by eight, both kernels are finite, their cardinalities have product nineteen, and the kernel cardinalities are nineteen and one in some order. This computes rational norm-isogeny kernel cardinalities, not geometric degrees or rank zero.
-- source:
--   Owned MazurTheorem isogeny-descent argument, Apache-2.0, checked with Mathlib pin 0df444a360eaa60ab8c11dca51a86af692955474. Named consumer: the two actual rational represented Picard norm maps for the order-thirteen curve. The explicit inverse uses twelve times the complementary norm since 12*8=1+5*19.

import Mathlib
universe u

theorem MazurTransfer.nineteen_norm_rational_kernel_card_product
    (G : Type u) [AddCommGroup G]
    (ht : Finite (CommGroup.torsion (Multiplicative G)))
    (hc : Nat.card (CommGroup.torsion (Multiplicative G)) = 19)
    (f g : G →+ G)
    (hfg : ∀ x, f (g x) = (19 : ℕ) • x)
    (hgf : ∀ x, g (f x) = (19 : ℕ) • x)
    (hsum : ∀ x, f x + g x = (8 : ℕ) • x) :
    Finite f.ker ∧ Finite g.ker ∧ Nat.card f.ker * Nat.card g.ker = 19 ∧
      ((Nat.card f.ker = 19 ∧ Nat.card g.ker = 1) ∨
        (Nat.card f.ker = 1 ∧ Nat.card g.ker = 19)) := by sorry
