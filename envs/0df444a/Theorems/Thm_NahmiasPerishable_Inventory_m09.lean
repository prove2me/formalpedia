-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m09
-- name    : NahmiasPerishable.Inventory.m09
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:29:05.855011+00:00
-- url     : https://prove2.me/theorems/6e2d122d-8130-470d-9297-687fe6ff393f
-- title:
--   Continuous-review cost unimodality and parameter reduction
-- statement:
--   He shows that −C(S) is unimodal and that the optimal S is a function of four variables: λK/h, λ(c − r)h, λd and λ(v + r)h.
--
--   Differences from the source:
--   - encoding: C(S) obtained from regenerative cycles → Poisson finite sums for expected cycle cost divided by expected cycle duration; reason: S is a positive integer and cycle duration has positive expectation; all four printed parameter combinations, including products with h, are retained
--   - encoding: unimodality and dependence of optimal S on four parameters → a maximizer of −C with monotonicity on either side, and equality of optimal-order sets for matching parameters; reason: ties are represented as sets without changing the optimizer claim
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.a(iv), Continuous-review cost unimodality and parameter reduction (unnumbered), p. 687 (PDF 8), DOI:10.1287/opre.30.4.680; review attribution: Weiss [1980].

import Definitions.Def_NahmiasPerishable_Inventory_Continuous

namespace NahmiasPerishable.Inventory

theorem m09 :
    (∀ P : WeissParams, ValidWeiss P → ∃ S : ℕ, S ∈ weissOptima P ∧
      (∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ S → -weissCost P i ≤ -weissCost P j) ∧
      (∀ i j : ℕ, S ≤ i → i ≤ j → -weissCost P j ≤ -weissCost P i)) ∧
    (∀ P Q : WeissParams, ValidWeiss P → ValidWeiss Q →
      weissParameters P = weissParameters Q → weissOptima P = weissOptima Q) := by sorry

end NahmiasPerishable.Inventory
