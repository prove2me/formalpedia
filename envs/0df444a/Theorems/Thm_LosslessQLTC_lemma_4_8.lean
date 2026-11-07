-- Prove2me | Theorems.Thm_LosslessQLTC_lemma_4_8
-- name    : LosslessQLTC.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:23:40.1866+00:00
-- url     : https://prove2.me/theorems/bd5b0736-25b3-46f6-8f6a-dc7494be0c3d
-- title:
--   Lemma 4.8, p.36 — heavy-mass propagation
-- statement:
--   Let $X$ be lossless, with $\|H_r\|\le c\|V_r\|$ for $c$ as in (4.26). For every $1\le i\le r$, if $\gamma_{i-1}>\sum_{j\in[k]}\varepsilon_j$, then
--
--   $$\|H_{i-1}\|\le\frac{i}{\gamma_{i-1}-\sum_{j\in[k]}\varepsilon_j}\|H_i\|.$$
--
--   The same holds for $i=r+1$ under the convention $\gamma_r=k-r$. So the mass of heavy vertices one level down is controlled by the mass at the current level.
--
--   Differences from the source:
--   - reading: Section 4's blanket assumption that every set to which lossless expansion is applied is in the lossless range → the hypothesis $\|H_r\|\le c\|V_r\|$ with $c$ of (4.26); reason: p.27 says this choice of $c$ ensures the assumption, and it is the form Theorem 4.10 uses
--   - encoding: the case $i=r+1$ under the convention $\gamma_r=k-r$ → a second clause with $\gamma_r$ written out as $k-r$; reason: the same statement; the function $\gamma$ is read only at $i<r$
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: the heavy set $H_r\subseteq V_r$ → a cochain $f$ with $H_r=\operatorname{supp}f$, thresholds $\gamma:\mathbb N\to\mathbb R$ used at $i<r$; reason: the source identifies a cochain with its support; same instances
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Lemma 4.8, p.36, eq. (4.21); p.27

import Mathlib
import Definitions.Def_LosslessQLTC_Heavy
import Definitions.Def_LosslessQLTC_IsLossless

namespace LosslessQLTC

/-- Lemma 4.8 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.36): for every `1 ≤ i ≤ r`, if
`γ_{i−1} > Σ_j ε_j` then `∥H_{i−1}∥ ≤ (i / (γ_{i−1} − Σ_j ε_j)) ∥H_i∥` (4.21). The same holds for
`i = r + 1` under the convention `γ_r = k − r`.

**Formalization Note.** The second clause is the case `i = r + 1`, with `γ_r` written `k − r`.
Section 4's blanket lossless range is the hypothesis `∥H_r∥ ≤ c∥V_r∥` (p.27). -/
theorem lemma_4_8 {k r : ℕ} (X : SquareComplex k) (hr : r < k) (f : Level X r → ZMod 2)
    (γ : ℕ → ℝ) (hγ : IsThresholds k r γ) (c ε : Fin k → ℝ) (hl : IsLossless X c ε)
    (hsmall : normC X f ≤ cConst X.D X.D' c * levelMass X r) :
    (∀ i, 1 ≤ i → i ≤ r → epsStar ε < γ (i - 1) →
      setNorm X (heavyLevel X f γ (i - 1)) ≤
        ((i : ℝ) / (γ (i - 1) - epsStar ε)) * setNorm X (heavyLevel X f γ i)) ∧
    (epsStar ε < (k : ℝ) - r →
      setNorm X (heavyLevel X f γ r) ≤
        (((r + 1 : ℕ) : ℝ) / ((k : ℝ) - r - epsStar ε)) *
          setNorm X (heavyLevel X f γ (r + 1))) := by sorry

end LosslessQLTC
