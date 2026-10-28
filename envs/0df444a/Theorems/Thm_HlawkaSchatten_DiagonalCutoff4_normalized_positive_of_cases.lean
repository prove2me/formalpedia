-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_normalized_positive_of_cases
-- name    : HlawkaSchatten.DiagonalCutoff4.normalized_positive_of_cases
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:48:16.410577+00:00
-- url     : https://prove2.me/theorems/5b3e3a33-ab67-4527-83aa-ecec4795ac9d
-- title:
--   Normalize a Hlawka counterexample using canonical chart certificates
-- statement:
--   For p greater than one, the displayed envelope bound and canonical chart implications produce a normalized positive frame with pair-tail ratios at most two fifths from every strict counterexample. Separate coarse parameters may be used for repeated-coordinate exclusion and sign localization; the fine lower bound k is retained in the frame.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.normalized_positive_of_cases {p q k d0 kc Ac dc ks As ds : ℝ}
    (hp : 1 < p) (hq0 : 0 < q) (hq1 : q < 1) (hk : 1 ≤ k)
    (hkc : kc ≤ k) (hks : ks ≤ k) (hAc : 3*q ≤ Ac) (hAs : 3*q ≤ As)
    (hd0 : 0 ≤ d0) (hdc : dc ≤ d0) (hds : ds ≤ d0) (hdroot : d0*(3:ℝ)^(1/p) ≤ 1)
    (hrep : ∀ c : Fin 323, ∀ X : Fin 3 → Fin 3 → ℝ,
      OrderedChart p kc Ac dc X (repeatedOrders c) (repeatedSigns c) → False)
    (hneg : ∀ c : Fin 88, c ≠ 63 → c ≠ 87 → ∀ X : Fin 3 → Fin 3 → ℝ,
      OrderedChart p ks As ds X (distinctOrders c) (distinctSigns c) → False)
    (hpos : ∀ c : Fin 88, c=63 ∨ c=87 → ∀ X : Fin 3 → Fin 3 → ℝ,
      OrderedChart p ks As ds X (distinctOrders c) (fun _ _ => true) →
      ∀ i h, i ≠ h → |pair X i h| ≤ (2/5:ℝ)*pair X i i)
    (hlinear : k < cyclicConstant p) (henvelope : scalarEnvelope p q < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ Y : Fin 3 → Fin 3 → ℝ, Frame p k (3*q) ds Y ∧
      (∀ i h, i ≠ h → 0 ≤ pair Y i h) ∧
      (∀ i h, i ≠ h → |pair Y i h| ≤ (2/5:ℝ)*pair Y i i) ∧
      tripleDeficit p (cyclicConstant p) Y < 0 := by sorry
