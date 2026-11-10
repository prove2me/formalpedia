-- Prove2me | Theorems.Thm_NogoodColoring1137_Main_slice_inequality
-- name    : NogoodColoring1137.Main.slice_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T17:01:26.294127+00:00
-- url     : https://prove2.me/theorems/f6308333-b7f2-408f-8d9a-02b782d2b22e
-- title:
--   Lemma 4.2 — Slice inequality and both contraction factors
-- statement:
--   Let $1\le\ell\le n$, $d_v\ge2$, $\sigma=\max_vd_v$, and let $W$ certify every active $\ell$-scope. With the strict-below-$\ell$ potential, every active $v$ satisfies
--   $$\sum_{b\in D_v}\Phi(U\setminus\{v\},W_v^b)\le(d_v-1)\Phi(U,W).$$
--   Every minimum-potential label $\mu$ satisfies both contractions:
--   $$\Phi(U\setminus\{v\},W_v^\mu)\le\frac{d_v-1}{d_v}\Phi(U,W)\le\frac{\sigma-1}{\sigma}\Phi(U,W).$$
--   This combinatorial table estimate does not require soundness for a code. It bounds exceptional positions.
--
--   **Formalization Note** Domain lower bounds are standing assumptions of §4 p.9. The exact-$\ell$ boundary is certified and both denominators are positive.
--
--   Differences from the source:
--   - encoding: finite coordinates and heterogeneous finite domains → Fin n and Fin (d v), with dependent words on scopes; reason: independent bijective relabeling preserves all words, certificates, boxes and counts
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Lemma 4.2, p.11, equations (5)–(6)

import Definitions.Def_NogoodColoring1137_Main_Codes

namespace NogoodColoring1137.Main

/-- Lemma 4.2, p.11: equations (5) and (6), both contraction factors. -/
theorem slice_inequality {n : ℕ} (d : Fin n → ℕ) (hd : ∀ v, 2 ≤ d v)
    (ell : ℕ) (hell : 1 ≤ ell ∧ ell ≤ n)
    (U : Finset (Fin n)) (W : Table d) (v : U)
    (hvalid : TableValid ell U W) (hcomplete : CompleteAt ell U W) :
    (∑ b : Fin (d v.val), Potential ell (U.erase v.val) (SliceTable v.val b W)) ≤
      (d v.val - 1) * Potential ell U W ∧
    ∀ mu : Fin (d v.val),
      (∀ b, Potential ell (U.erase v.val) (SliceTable v.val mu W) ≤
        Potential ell (U.erase v.val) (SliceTable v.val b W)) →
      (Potential ell (U.erase v.val) (SliceTable v.val mu W) : ℝ) ≤
        ((d v.val : ℝ)-1) / d v.val * Potential ell U W ∧
      ((d v.val : ℝ)-1) / d v.val * Potential ell U W ≤
        ((Sigma d : ℝ)-1) / Sigma d * Potential ell U W := by sorry

end NogoodColoring1137.Main
