-- Prove2me | Theorems.Thm_LosslessQLTC_lemma_4_7
-- name    : LosslessQLTC.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:23:27.14795+00:00
-- url     : https://prove2.me/theorems/5d53891c-f082-457a-aaef-4dd88ab95a23
-- title:
--   Lemma 4.7, p.34 — light squares are controlled by imbalance and thresholds
-- statement:
--   Let $X$ be lossless, with $\|H_r\|\le c\|V_r\|$ for $c$ as in (4.26). For every $2\le i\le r+1$,
--
--   $$\|\mathrm{Light}_i\|\le(i-1)(k-i+1)\max_{s<t}\{\varepsilon_tD'_s,\gamma_{i-2}\}\|H_{i-1}\|,$$
--
--   with the maximum over $1\le s<t\le k$. Imbalance enters the argument here.
--
--   Differences from the source:
--   - reading: Section 4's blanket assumption that every set to which lossless expansion is applied is in the lossless range → the hypothesis $\|H_r\|\le c\|V_r\|$ with $c$ of (4.26); reason: p.27 says this choice of $c$ ensures the assumption, and it is the form Theorem 4.10 uses
--   - encoding: $\max_{s<t}\{\varepsilon_tD'_s,\gamma_{i-2}\}$ → any upper bound $M$ of all $\varepsilon_tD'_s$, $s<t$, and of $\gamma_{i-2}$; reason: the maximum is such an $M$, and the bound for it implies the bound for every larger $M$
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: the heavy set $H_r\subseteq V_r$ → a cochain $f$ with $H_r=\operatorname{supp}f$, thresholds $\gamma:\mathbb N\to\mathbb R$ used at $i<r$; reason: the source identifies a cochain with its support; same instances
--   - reading: $H_r(t)$, $\|\mathrm{Same}_i\|$, $\|\mathrm{Light}_i\|$ used without a printed definition → $H_r\cap H(t)$, $\sum_{a\in H_i}\|a\|\mathrm{Same}(a)$, $\sum_{a\in H_i}\|a\|\mathrm{Light}(a)$; reason: their use on pp.29–32 and p.39 fixes these
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Lemma 4.7, p.34, eq. (4.18); p.27; p.36

import Mathlib
import Definitions.Def_LosslessQLTC_Heavy
import Definitions.Def_LosslessQLTC_IsLossless

namespace LosslessQLTC

/-- Lemma 4.7 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.34): for every `2 ≤ i ≤ r + 1`,
`∥Light_i∥ ≤ (i − 1)(k − i + 1) max_{s<t} {ε_t D′_s, γ_{i−2}} ∥H_{i−1}∥` (4.18), the maximum over
`1 ≤ s < t ≤ k` (p.36).

**Formalization Note.** The maximum is stated through its universal property: `M` is any upper bound
of all `ε_t D′_s`, `s < t`, and of `γ_{i−2}`, and the maximum is such an `M`. Section 4's blanket
lossless range is the hypothesis `∥H_r∥ ≤ c∥V_r∥` (p.27). -/
theorem lemma_4_7 {k r : ℕ} (X : SquareComplex k) (hr : r < k) (f : Level X r → ZMod 2)
    (γ : ℕ → ℝ) (hγ : IsThresholds k r γ) (c ε : Fin k → ℝ) (hl : IsLossless X c ε)
    (hsmall : normC X f ≤ cConst X.D X.D' c * levelMass X r) (i : ℕ) (hi1 : 2 ≤ i)
    (hi2 : i ≤ r + 1) (M : ℝ) (hM : ∀ s t : Fin k, s < t → ε t * (X.D' s : ℝ) ≤ M)
    (hMγ : γ (i - 2) ≤ M) :
    lightNorm X f γ i ≤
      ((i : ℝ) - 1) * ((k : ℝ) - i + 1) * M * setNorm X (heavyLevel X f γ (i - 1)) := by sorry

end LosslessQLTC
