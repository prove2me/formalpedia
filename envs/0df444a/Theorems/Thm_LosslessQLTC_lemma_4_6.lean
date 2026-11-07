-- Prove2me | Theorems.Thm_LosslessQLTC_lemma_4_6
-- name    : LosslessQLTC.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:23:34.644148+00:00
-- url     : https://prove2.me/theorems/facaa72d-882c-457d-828a-e3e2ce533bc3
-- title:
--   Lemma 4.6, p.34 — same-type collisions are controlled by the loss
-- statement:
--   Let $X$ be lossless, with $\|H_r\|\le c\|V_r\|$ for $c$ as in (4.26). For every $1\le i\le r+1$,
--
--   $$\|\mathrm{Same}_i\|\le\Big(\sum_{j=1}^k\varepsilon_j\Big)\|H_{i-1}\|.$$
--
--   Same-type collisions are thus small relative to the heavy mass one level down.
--
--   Differences from the source:
--   - reading: Section 4's blanket assumption that every set to which lossless expansion is applied is in the lossless range → the hypothesis $\|H_r\|\le c\|V_r\|$ with $c$ of (4.26); reason: p.27 says this choice of $c$ ensures the assumption, and it is the form Theorem 4.10 uses
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: the heavy set $H_r\subseteq V_r$ → a cochain $f$ with $H_r=\operatorname{supp}f$, thresholds $\gamma:\mathbb N\to\mathbb R$ used at $i<r$; reason: the source identifies a cochain with its support; same instances
--   - reading: $H_r(t)$, $\|\mathrm{Same}_i\|$, $\|\mathrm{Light}_i\|$ used without a printed definition → $H_r\cap H(t)$, $\sum_{a\in H_i}\|a\|\mathrm{Same}(a)$, $\sum_{a\in H_i}\|a\|\mathrm{Light}(a)$; reason: their use on pp.29–32 and p.39 fixes these
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Lemma 4.6, p.34, eq. (4.17); p.27

import Mathlib
import Definitions.Def_LosslessQLTC_Heavy
import Definitions.Def_LosslessQLTC_IsLossless

namespace LosslessQLTC

/-- Lemma 4.6 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.34): for every `1 ≤ i ≤ r + 1`,
`∥Same_i∥ ≤ (Σ_j ε_j) ∥H_{i−1}∥` (4.17).

**Formalization Note.** Section 4 assumes that every set to which lossless expansion is applied lies
in the lossless range, and says that `c` of (4.26) ensures this whenever `∥H_r∥ ≤ c∥V_r∥` (p.27).
The hypothesis here is that bound. -/
theorem lemma_4_6 {k r : ℕ} (X : SquareComplex k) (hr : r < k) (f : Level X r → ZMod 2)
    (γ : ℕ → ℝ) (hγ : IsThresholds k r γ) (c ε : Fin k → ℝ) (hl : IsLossless X c ε)
    (hsmall : normC X f ≤ cConst X.D X.D' c * levelMass X r) (i : ℕ) (hi1 : 1 ≤ i)
    (hi2 : i ≤ r + 1) :
    sameNorm X f γ i ≤ epsStar ε * setNorm X (heavyLevel X f γ (i - 1)) := by sorry

end LosslessQLTC
