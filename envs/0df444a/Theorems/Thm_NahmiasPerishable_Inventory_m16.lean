-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m16
-- name    : NahmiasPerishable.Inventory.m16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:28:37.871727+00:00
-- url     : https://prove2.me/theorems/a89264e6-aecb-4315-9b12-83c0596363fd
-- title:
--   Fixed-order-quantity stock process and expiry criterion
-- statement:
--   If q, the number of fresh units entering stock each period, is fixed then the total stock on hand at the end of each period, Yₜ, will form a stationary Markov chain. Then the (m − 1) dimensional vector of on hand stocks at the end of each period will be of the form: (q, q, ⋯, q, s, 0, ⋯, 0) where 0 ≤ s ≤ q. Note that stock will perish if and only if (m − 2)q ≤ Yₜ ≤ (m − 1)q, since only in that case will the final component of the state vector be positive. The number of units which perish will be exactly Yₜ − (m − 2)q.
--
--   Differences from the source:
--   - encoding: lifetime m and n remaining periods → k = m−1 age coordinates and objective index n−1; reason: the recursion value n has n periods and objective j chooses the first order for j+1 periods
--   - reading: stationary Markov chain of ending stocks → time-homogeneous scalar transition after the arbitrary initial inventory has aged out; reason: distributional stationarity is not asserted for an arbitrary initial state; all later periods and arbitrary nonnegative demand laws are included
--   - reading: stock will perish, identified in the paragraph with a positive final age component → actual expiration during the period ending at the reported state, with the printed closed-interval criterion and amount; reason: expiration is computed from FIFO service before aging and is not redefined by the claimed formula; the printed endpoint conflict I4 remains
--   - encoding: youngest-first packed vector → oldest-first packedStock reconstructed from Y; reason: coordinate reversal changes no inventory amounts
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.b(iii), Fixed-order-quantity stock process and expiry criterion (unnumbered), p. 690 (PDF 11), DOI:10.1287/opre.30.4.680; review attribution: Brodheim, Derman and Prastacos [1975].

import Definitions.Def_NahmiasPerishable_Inventory_Stationary

open MeasureTheory

namespace NahmiasPerishable.Inventory

theorem m16 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ d ∂μ, 0 ≤ d) (k : ℕ) (hk : 1 ≤ k) (q : ℝ) (hq : 0 < q)
    (x : AgeState k) (hx : canonical false x) :
    MarkovFromShocks μ
      (fun d t => total (trajectory false x (fun _ => q) d (t+k)))
      (constantStep k q) ∧
    Measurable (fun yd : ℝ × ℝ => constantStep k q yd.1 yd.2) ∧
    (∀ d : ℕ → ℝ, (∀ t, 0 ≤ d t) → ∀ t,
      let X := trajectory false x (fun _ => q) d
      let Y := total (X (t+k))
      let E := expires (X (t+k-1)) (d (t+k-1))
      (X (t+k)).1 = packedStock k q Y ∧
      0 ≤ Y ∧ Y ≤ k*q ∧
      total (X (t+k+1)) = constantStep k q Y (d (t+k)) ∧
      (0 < E ↔ (k-1)*q ≤ Y ∧ Y ≤ k*q) ∧
      ((k-1)*q ≤ Y → Y ≤ k*q → E = Y-(k-1)*q)) := by sorry

end NahmiasPerishable.Inventory
