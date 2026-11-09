-- Prove2me | Theorems.Thm_MWCSherali_lemma_2_4
-- name    : MWCSherali.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:16:38.230438+00:00
-- url     : https://prove2.me/theorems/2de7accc-63c5-4f8e-a529-97b3d8853e84
-- title:
--   Lemma 2.4 — the vertex-consistency LP is a relaxation
-- statement:
--   Let $n\ge1$ and let $w:E_{k,n}\to\mathbb R_{\ge0}$. Then
--
--   $$\mathrm{LP}^{\mathrm{no}}_{\mathrm{vertex}}(w)\le\mathrm{OPT}^{\mathrm{no}}(w).$$
--
--   Every non-opposite cut is a feasible point of the LP with the same value, so a lower bound on the LP value is a lower bound on the minimum non-opposite cut.
--
--   Differences from the source:
--   - encoding: n a positive integer (p.4) → hypothesis 0 < n; reason: Δ_{k,n} is defined only for positive n
--   - encoding: points x ∈ Δ_{k,n} with coordinates in (1/n)ℤ, 1-based indices → integer coordinates y = n x (Grid k n), 0-based indices; reason: Lean convention; the same points
--   - encoding: w : E_{k,n} → ℝ_{≥0} → w : Sym2 (Grid k n) → ℝ, nonnegative on E_{k,n}; reason: only the values on E_{k,n} are ever used
--   - encoding: labels [k+1] with neutral label k+1 → labels Fin (k+1), terminal i as i − 1, neutral label as Fin.last k; reason: Lean convention; same labelings
--   - encoding: cells C ∈ D_{k,n} → cells indexed by V ∈ Δ_{k,n+1} (Grid k (n+1)); reason: the paper's one-to-one correspondence D_{k,n} ↔ Δ_{k,n+1} (p.15)
--   - encoding: p_e defined through D(e), the unique cell containing e → the cell indexed by the coordinatewise maximum x ∨ y of e = {x, y}; reason: this is the cell D((n x + e_j)/(n+1)) of the proof of Lemma 2.3, the unique cell containing e
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 2.4, p.16

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_edges
import Definitions.Def_MWCSherali_OPTno
import Definitions.Def_MWCSherali_LPvertex

namespace MWCSherali

/-- **Lemma 2.4 (the vertex-consistency LP is a relaxation).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 2.4, p.16:
"For any `w : E_{k,n} → ℝ_{≥0}`, we have `LP^no_vertex(w) ≤ OPT^no(w)`."

**Formalization Note.** `w : E_{k,n} → ℝ_{≥0}` is a function on `Sym2 (Grid k n)` that is
nonnegative on `E_{k,n}`; its other values are never used. The paper's `n` is a positive
integer. -/
theorem lemma_2_4 (k n : ℕ) (hn : 0 < n) (w : Sym2 (Grid k n) → ℝ)
    (hw : ∀ e ∈ edges k n, 0 ≤ w e) :
    LPvertex w ≤ OPTno w := by sorry

end MWCSherali
