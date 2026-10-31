-- Prove2me | Theorems.Thm_MultimodularDocks_marginal_dock
-- name    : MultimodularDocks.marginal_dock
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:35:28.261285+00:00
-- url     : https://prove2.me/theorems/1e2b0567-c601-4053-819b-0e1a45e4cd64
-- title:
--   Lemma 3.3, Cases 1.)–2.), (7) (corrected: Definition 1 on the quadrant) — station inequalities for a moved dock
-- statement:
--   Let $f$ be multimodular and $d,b,d',b'\ge 0$.
--
--   1. If $d<d'$ and $d+b<d'+b'$, then $f(d,b)-f(d+1,b)\ge f(d'-1,b')-f(d',b')$.
--   2. If $d'<d$ and $d'+b'<d+b$, then $f(d-1,b)-f(d,b)\le f(d',b')-f(d'+1,b')$. $\quad(7)$
--   3. If $b<b'$ and $d+b<d'+b'$, then $f(d,b)-f(d,b+1)\ge f(d',b'-1)-f(d',b')$.
--   4. If $b'<b$ and $d'+b'<d+b$, then $f(d,b-1)-f(d,b)\le f(d',b')-f(d',b'+1)$.
--
--   In words: a station with fewer docks than in a better allocation gains at least as much from one more empty (full) dock as the better allocation loses by giving one up, and symmetrically for a station with too many docks.
--
--   Differences from the source:
--   - correction: Definition 1 (p.10): (1)–(3) for all d, b ∈ ℤ for f : ℤ² → ℝ ∪ {∞} with ∞ − ∞ = ∞, station costs c_i = ∞ off their band (p.11) → IsMultimodular: a real f : ℤ → ℤ → ℝ satisfies (1)–(3) whenever all arguments are ≥ 0; the band is carried separately (InBand, Feasible); reason: with the printed convention Lemma 2.1 is false (X empty, l = 0, u = 2, so c_i = 0 on its band: (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞); the other reading, (1)–(3) whenever all four terms are finite, makes Theorem 1 false (two stations, l = u = 2, B = D = 2, g_A(2 − k, k) = 1, 3, 0 for k = 0, 1, 2, g_B = 0: from b = (0, 2) Algorithm 1 stops at cost 1 while (2, 0) costs 0 at dock-move distance 0)
--   - generalization: inequalities for the station UDFs c_j, c_k at (d_j, b_j), (d⋆_j, b⋆_j) inside the proof of Lemma 3.3, Case 1.), with Cases 2.) and 3.b) 'symmetric' → four inequalities for any multimodular f and any nonnegative (d, b), (d', b') with the stated order relations; reason: the page's derivation uses only (3) and (6), resp. (1) and (2); the station UDFs are multimodular by Lemma 2.1; clauses 3–4 write out the symmetric cases
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, proof of Lemma 3.3, App. C.2.1, Case 1.), pp.46–47, inequality (7); symmetric cases p.46 and p.48

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular

namespace MultimodularDocks

/-- **Station inequalities for a moved dock** (Freund, Henderson, Shmoys, arXiv:1611.09304v5,
proof of Lemma 3.3, App. C.2.1, Case 1.), pp.46–47, inequality (7), and the symmetric
Case 2.) and Case 3.b) bounds of p.48). Let `f` be multimodular and `d, b, d', b' ≥ 0`.
1. If `d < d'` and `d + b < d' + b'`: `f(d, b) − f(d + 1, b) ≥ f(d' − 1, b') − f(d', b')`.
2. If `d' < d` and `d' + b' < d + b`: `f(d − 1, b) − f(d, b) ≤ f(d', b') − f(d' + 1, b')` (7).
3. If `b < b'` and `d + b < d' + b'`: `f(d, b) − f(d, b + 1) ≥ f(d', b' − 1) − f(d', b')`.
4. If `b' < b` and `d' + b' < d + b`: `f(d, b − 1) − f(d, b) ≤ f(d', b') − f(d', b' + 1)`.

**Formalization Note** Clauses 3 and 4 are the cases the page calls symmetric (full docks in
place of empty docks), written out. -/
theorem marginal_dock (f : ℤ → ℤ → ℝ) (hf : IsMultimodular f) (d b d' b' : ℤ)
    (hd : 0 ≤ d) (hb : 0 ≤ b) (hd' : 0 ≤ d') (hb' : 0 ≤ b') :
    (d < d' → d + b < d' + b' → f (d' - 1) b' - f d' b' ≤ f d b - f (d + 1) b) ∧
      (d' < d → d' + b' < d + b → f (d - 1) b - f d b ≤ f d' b' - f (d' + 1) b') ∧
      (b < b' → d + b < d' + b' → f d' (b' - 1) - f d' b' ≤ f d b - f d (b + 1)) ∧
      (b' < b → d' + b' < d + b → f d (b - 1) - f d b ≤ f d' b' - f d' (b' + 1)) := by sorry

end MultimodularDocks
