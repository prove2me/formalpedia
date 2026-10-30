-- Prove2me | Theorems.Thm_JuschenkoMonod_finite_symmDiff_natSet_image
-- name    : JuschenkoMonod.finite_symmDiff_natSet_image
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:27:21.844982+00:00
-- url     : https://prove2.me/theorems/ee7c724a-3b6d-4ec7-9b7c-8a2ad6107a62
-- title:
--   p. 784 — ℕ △ g(ℕ) is finite for every g ∈ W(ℤ)
-- statement:
--   For every $g \in W(\mathbf Z)$, the symmetric difference $\mathbf N \mathbin{\triangle} g(\mathbf N)$ is finite, where $\mathbf N = \{0, 1, 2, \dots\} \subseteq \mathbf Z$.
--
--   *Formalization note.* $\mathbf N$ is taken to contain $0$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 784, the remark before Proposition 3.3

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem finite_symmDiff_natSet_image (g : Equiv.Perm ℤ) (hg : g ∈ IntervalExchange.wobbling ℤ) :
    (symmDiff natSet (g '' natSet)).Finite := by
  sorry

end JuschenkoMonod
