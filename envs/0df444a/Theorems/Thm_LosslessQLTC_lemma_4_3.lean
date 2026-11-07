-- Prove2me | Theorems.Thm_LosslessQLTC_lemma_4_3
-- name    : LosslessQLTC.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:21:32.867146+00:00
-- url     : https://prove2.me/theorems/e11b7ccf-e75c-4caa-9332-03484ba84332
-- title:
--   Lemma 4.3, p.31 — recursive excess bound
-- statement:
--   For every heavy vertex $a\in H$,
--
--   $$E(a)\le\mathrm{Same}(a)+\mathrm{Light}(a)+\sum_{x\in\mathrm{Ch}(a)}E(x).$$
--
--   So excess at $a$ comes only from excess at its heavy children and from the two local charges at $a$.
--
--   Differences from the source:
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: the heavy set $H_r\subseteq V_r$ → a cochain $f$ with $H_r=\operatorname{supp}f$, thresholds $\gamma:\mathbb N\to\mathbb R$ used at $i<r$; reason: the source identifies a cochain with its support; same instances
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Lemma 4.3, p.31, eq. (4.12)

import Mathlib
import Definitions.Def_LosslessQLTC_Heavy

namespace LosslessQLTC

/-- Lemma 4.3 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.31): for every heavy vertex `a`,
`E(a) ≤ Same(a) + Light(a) + Σ_{x ∈ Ch(a)} E(x)` (4.12). -/
theorem lemma_4_3 {k r : ℕ} (X : SquareComplex k) (hr : r < k) (f : Level X r → ZMod 2)
    (γ : ℕ → ℝ) (hγ : IsThresholds k r γ) (a : X.Vtx) (ha : a ∈ heavy X f γ) :
    excess X f γ a ≤ same X f γ a + light X f γ a + ∑ x ∈ Ch X f γ a, excess X f γ x := by sorry

end LosslessQLTC
