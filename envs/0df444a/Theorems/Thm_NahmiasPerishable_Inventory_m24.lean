-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m24
-- name    : NahmiasPerishable.Inventory.m24
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:28:21.14054+00:00
-- url     : https://prove2.me/theorems/ea341a74-b9cc-4333-be18-d134eb3a3ecc
-- title:
--   Printed Emmons stationary-density equations
-- statement:
--   Then he shows that the stationary density g(x) of ending stocks, x, satisfies the differential equations
--   g′(x) = g(x), Se⁻²ᶿ < x < Se⁻ᶿ or x < se⁻ᶿ
--   g′(x) = g(x) − eᶿg(xeᶿ), se⁻ᶿ < x < Se⁻²ᶿ.
--
--   Differences from the source:
--   - reading: e^(−θ) is called the fraction lost while it scales the displayed stock intervals → e^(−θ) is the retained fraction in the actual (s,S) transition; reason: this follows the displayed equations; backlogs do not decay
--   - encoding: stationary density equations → existence of a nonnegative measurable version of the density of an invariant law satisfying both derivative identities; reason: the density is tied to the transition kernel; no exponential-demand hypothesis or differential-equation axiom is inserted
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §2.2.b, Printed Emmons stationary-density equations (unnumbered), p. 700 (PDF 21), DOI:10.1287/opre.30.4.680; review attribution: Emmons [1968].

import Definitions.Def_NahmiasPerishable_Inventory_Decay

open MeasureTheory Set

namespace NahmiasPerishable.Inventory

theorem m24 (D : Demand) (s S theta : ℝ) (hs : 0 ≤ s) (hS : s < S)
    (htheta : 0 < theta) (ν : Measure ℝ) (hν : emmonsInvariant D s S theta ν) :
    ∃ g : ℝ → ℝ, (∀ x, 0 ≤ g x) ∧ Measurable g ∧
      ν = volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      (∀ x, (S*Real.exp (-2*theta) < x ∧ x < S*Real.exp (-theta)) ∨
          x < s*Real.exp (-theta) → HasDerivAt g (g x) x) ∧
      (∀ x, s*Real.exp (-theta) < x → x < S*Real.exp (-2*theta) →
        HasDerivAt g (g x-Real.exp theta*g (x*Real.exp theta)) x) := by sorry

end NahmiasPerishable.Inventory
