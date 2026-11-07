-- Prove2me | Theorems.Thm_OnlineCAP_theorem_4_8
-- name    : OnlineCAP.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:24:32.403955+00:00
-- url     : https://prove2.me/theorems/ab3400c6-e07c-47a2-aea5-2f6a226193cc
-- title:
--   Theorem 4.8 — octants in ℝ³ have O(rκ²) distinct shallow traces [AT14]
-- statement:
--   There is an absolute constant $C_{\mathrm{dom}}$ such that for every orientation of octants, every finite set $W\subseteq\mathbb R^3$ of $r$ points and every integer $\kappa\ge1$,
--   $$\big|\{W\cap O : O\text{ an octant of the given orientation},\ 1\le|W\cap O|\le\kappa\}\big|\le C_{\mathrm{dom}}\,r\,\kappa^2 .$$
--
--   Here traces are counted as distinct sets. The bound, a consequence of the shallow cuttings for 3D dominance ranges of Afshani and Tsakalidis [AT14], is the geometric input of Lemma 4.7.
--
--   Differences from the source:
--   - reading: octants of a fixed orientation → every one of the eight orientations, with one constant C_dom for all; reason: "a fixed orientation" means any fixed one (Lemma 4.7 applies it to two orientations), and with finitely many orientations the constants combine into one
--   - encoding: octants in ℝ³ → closed octants {s : s_i ≤ q_i or s_i ≥ q_i}, points of ℝ³ as Fin 3 → ℝ; reason: Appendix A uses closed dominance ranges (−∞, q_x] × (−∞, q_y] × (−∞, q_z]
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 4.8, p.19 (proof Appendix A, pp.27–28)

import Mathlib
import Definitions.Def_OnlineCAP_octant

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

open Classical in
/-- **Theorem 4.8 (3D octant shallow traces [AT14]).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Theorem 4.8, p.19 (PDF p.19), proof
in Appendix A, pp.27–28: "There exists an absolute constant Cdom such that for any r-element point
set in R3, the number of distinct nonempty traces of size at most κ under octants of a fixed
orientation is at most Cdom r κ², for every integer κ ≥ 1."

There is a constant `C_dom` such that for every orientation `σ`, every finite `W ⊆ ℝ³` and every
integer `κ ≥ 1`, the number of distinct sets `S = W ∩ O`, `O` an octant of orientation `σ`, with
`1 ≤ |S| ≤ κ`, is at most `C_dom |W| κ²`.

**Formalization Note.** One constant for all eight orientations ("a fixed orientation": any
one); Lemma 4.7 uses two of them. Octants are closed. -/
theorem theorem_4_8 : ∃ C_dom : ℝ, ∀ (σ : Fin 3 → Bool) (W : Finset (Fin 3 → ℝ)) (κ : ℕ),
    1 ≤ κ →
    ((W.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ κ ∧
        ∃ q : Fin 3 → ℝ, W.filter (fun s => s ∈ octant σ q) = S)).card : ℝ) ≤
      C_dom * W.card * (κ : ℝ) ^ 2 := by sorry

end OnlineCAP
