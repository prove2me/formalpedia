-- Prove2me | Theorems.Thm_LosslessQLTC_corollary_4_9
-- name    : LosslessQLTC.corollary_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:24:02.463914+00:00
-- url     : https://prove2.me/theorems/a015a7dc-f751-4a12-b6ea-cf27d7e9c313
-- title:
--   Corollary 4.9, p.37 — iterated heavy-mass propagation
-- statement:
--   Let $X$ be lossless, with $\|H_r\|\le c\|V_r\|$ for $c$ as in (4.26), and let $1\le i\le r+1$. Assume that $\gamma_{s-1}>\sum_{j\in[k]}\varepsilon_j$ for every $i\le s\le r$. Then
--
--   $$\|H_{i-1}\|\le\prod_{s=i}^r\frac{s}{\gamma_{s-1}-\sum_{j\in[k]}\varepsilon_j}\|H_r\|.$$
--
--   For $i=r+1$ the product is empty. This is the total price of pulling heaviness from level $r$ down to level $i-1$.
--
--   Differences from the source:
--   - reading: Section 4's blanket assumption that every set to which lossless expansion is applied is in the lossless range → the hypothesis $\|H_r\|\le c\|V_r\|$ with $c$ of (4.26); reason: p.27 says this choice of $c$ ensures the assumption, and it is the form Theorem 4.10 uses
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: the heavy set $H_r\subseteq V_r$ → a cochain $f$ with $H_r=\operatorname{supp}f$, thresholds $\gamma:\mathbb N\to\mathbb R$ used at $i<r$; reason: the source identifies a cochain with its support; same instances
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Corollary 4.9, p.37, eq. (4.24); p.27

import Mathlib
import Definitions.Def_LosslessQLTC_Heavy
import Definitions.Def_LosslessQLTC_IsLossless

namespace LosslessQLTC

/-- Corollary 4.9 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.37): for `1 ≤ i ≤ r + 1`, if
`γ_{s−1} > Σ_j ε_j` for every `i ≤ s ≤ r`, then
`∥H_{i−1}∥ ≤ ∏_{s=i}^r (s / (γ_{s−1} − Σ_j ε_j)) ∥H_r∥` (4.24). The case `i = r + 1` is the empty
product.

**Formalization Note.** Section 4's blanket lossless range is the hypothesis `∥H_r∥ ≤ c∥V_r∥`
(p.27). -/
theorem corollary_4_9 {k r : ℕ} (X : SquareComplex k) (hr : r < k) (f : Level X r → ZMod 2)
    (γ : ℕ → ℝ) (hγ : IsThresholds k r γ) (c ε : Fin k → ℝ) (hl : IsLossless X c ε)
    (hsmall : normC X f ≤ cConst X.D X.D' c * levelMass X r) (i : ℕ) (hi1 : 1 ≤ i)
    (hi2 : i ≤ r + 1) (hs : ∀ s, i ≤ s → s ≤ r → epsStar ε < γ (s - 1)) :
    setNorm X (heavyLevel X f γ (i - 1)) ≤
      (∏ s ∈ Finset.Icc i r, ((s : ℝ) / (γ (s - 1) - epsStar ε))) *
        setNorm X (heavyLevel X f γ r) := by sorry

end LosslessQLTC
