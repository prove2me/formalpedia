-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m13
-- name    : NahmiasPerishable.Inventory.m13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:26:28.971414+00:00
-- url     : https://prove2.me/theorems/bac37f09-587f-49b9-a3e6-c058563bf078
-- title:
--   FIFO minimizes cumulative outdating
-- statement:
--   In addition, they provide a rigorous proof that cumulative outdating is minimized under a FIFO issuing scheme.
--
--   Differences from the source:
--   - generalization: FIFO minimizes cumulative outdating in the discrete-demand discussion → a pathwise inequality for every nonnegative real demand and replenishment path, either shortage convention, and every horizon; reason: the deterministic FIFO interchange comparison applies to each discrete-demand realization; replenishments and initial stock are identical for both issuing rules
--   - encoding: admissible issuing schemes → work-conserving allocations of available units to demand, with no premature disposal; reason: the competing path is constructed from its issues and its own actual age state
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.b(ii), FIFO minimizes cumulative outdating (unnumbered), p. 689 (PDF 10), DOI:10.1287/opre.30.4.680; review attribution: Chazan and Gal [1977].

import Definitions.Def_NahmiasPerishable_Inventory_Issuance

namespace NahmiasPerishable.Inventory

theorem m13 (k : ℕ) (b : Bool) (x : AgeState k) (hx : physical x)
    (q d : ℕ → ℝ) (hq : ∀ t, 0 ≤ q t) (hd : ∀ t, 0 ≤ d t)
    (u : IssueRule k) (hu : FeasibleIssue u) (N : ℕ) :
    (∑ t ∈ Finset.range N,
      issueExpiry (fifoIssue k) t (issuePath (fifoIssue k) b x q d t) (q t) (d t)) ≤
    ∑ t ∈ Finset.range N, issueExpiry u t (issuePath u b x q d t) (q t) (d t) := by sorry

end NahmiasPerishable.Inventory
