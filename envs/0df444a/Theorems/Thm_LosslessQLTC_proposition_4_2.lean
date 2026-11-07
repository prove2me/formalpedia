-- Prove2me | Theorems.Thm_LosslessQLTC_proposition_4_2
-- name    : LosslessQLTC.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:20:48.450162+00:00
-- url     : https://prove2.me/theorems/2acbf3e0-3268-48c6-935d-d0fe15bf0095
-- title:
--   Proposition 4.2, p.30 — local-to-global comparison
-- statement:
--   Let $0\le r\le k-1$, let $H_r\subseteq V_r$, and let $0<\gamma_i<k-i$ be thresholds for $0\le i<r$. Then
--
--   $$\|\delta H_r\|\ge\sum_{t\in\mathrm{Ter}}\|\delta H_r(t)\|-(k-r)\|E_r\|-2\|E_{r+1}\|.$$
--
--   So the global coboundary is bounded below by the terminal-cluster coboundaries, up to the excess at levels $r$ and $r+1$. Neither lossless expansion nor minimality is assumed.
--
--   Differences from the source:
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: the heavy set $H_r\subseteq V_r$ → a cochain $f$ with $H_r=\operatorname{supp}f$, thresholds $\gamma:\mathbb N\to\mathbb R$ used at $i<r$; reason: the source identifies a cochain with its support; same instances
--   - reading: $H_r(t)$, $\|\mathrm{Same}_i\|$, $\|\mathrm{Light}_i\|$ used without a printed definition → $H_r\cap H(t)$, $\sum_{a\in H_i}\|a\|\mathrm{Same}(a)$, $\sum_{a\in H_i}\|a\|\mathrm{Light}(a)$; reason: their use on pp.29–32 and p.39 fixes these
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Proposition 4.2, p.30, eq. (4.7)

import Mathlib
import Definitions.Def_LosslessQLTC_Heavy

namespace LosslessQLTC

/-- Proposition 4.2 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.30):
`∥δH_r∥ ≥ Σ_{t ∈ Ter} ∥δH_r(t)∥ − (k − r) ∥E_r∥ − 2 ∥E_{r+1}∥` (4.7). -/
theorem proposition_4_2 {k r : ℕ} (X : SquareComplex k) (hr : r < k) (f : Level X r → ZMod 2)
    (γ : ℕ → ℝ) (hγ : IsThresholds k r γ) :
    (∑ t ∈ terminals X f γ, normC X (delta X r (clusterCochain X f γ t))) -
        ((k : ℝ) - r) * excessNorm X f γ r - 2 * excessNorm X f γ (r + 1) ≤
      normC X (delta X r f) := by sorry

end LosslessQLTC
