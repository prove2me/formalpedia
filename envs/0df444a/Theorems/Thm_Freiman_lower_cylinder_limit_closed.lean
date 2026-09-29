-- Prove2me | Theorems.Thm_Freiman_lower_cylinder_limit_closed
-- name    : Freiman.lower_cylinder_limit_closed
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:54.739866+00:00
-- url     : https://prove2.me/theorems/a91b7e9a-9246-45bc-b9a5-2953268bce56
-- title:
--   Freiman lower construction: cylinder limit closed
-- statement:
--   Prescribed physical prefixes, bounded outside digits, one of seven fixed cores and forbidden finite words persist under coordinate limits; the diverging subsequence eventually extends every earlier cylinder.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, lem:lc-cylinders

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_cylinder_limit_closed (h : ℕ → LowerPair) (he : ∀ n, lowerExtends (h n) (h (n+1)))
    (A : ℕ → ℤ → ℕ+) (ha : ∀ n, LowerModel (A n) ∧ lowerCylinder (h n) (A n))
    (v : ℕ → ℕ) (hv : StrictMono v) (a : ℤ → ℕ+)
    (hc : ∀ i : ℤ, ∀ᶠ n in Filter.atTop, A (v n) i = a i) :
    LowerModel a ∧ ∀ n, lowerCylinder (h n) a := by
  sorry
