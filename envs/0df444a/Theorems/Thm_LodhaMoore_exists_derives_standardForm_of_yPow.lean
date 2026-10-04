-- Prove2me | Theorems.Thm_LodhaMoore_exists_derives_standardForm_of_yPow
-- name    : LodhaMoore.exists_derives_standardForm_of_yPow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T08:41:06.129533+00:00
-- url     : https://prove2.me/theorems/7a31de4f-96cc-494d-9595-2ac88b900358
-- title:
--   Lemma 5.2 — y_s^{±1} derives a deep standard form supported below s
-- statement:
--   For every finite binary sequence $s$, every $l \in \mathbb N$, and $\varepsilon = \pm 1$, some standard form $\Omega$ can be derived from the one-letter word $y_s^\varepsilon$ such that: (1) every $x_u$ occurring in $\Omega$ has $u$ extending $s$; (2) every $y_u^n$ occurring in $\Omega$ has $u$ extending $s$, $|u| \ge l$ and $n = \pm 1$; (3) if $y_u$ and $y_v$ occur with $u \ne v$, then $u$ and $v$ are incompatible.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 10, Lemma 5.2

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_LodhaMooreWords

namespace LodhaMoore

theorem exists_derives_standardForm_of_yPow (s : Seq) (l : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ Ω, Derives [(.y s, ε)] Ω ∧ IsStandardForm Ω ∧
      (∀ u n, (Gen.x u, n) ∈ Ω → s <+: u) ∧
      (∀ u n, (Gen.y u, n) ∈ Ω → s <+: u ∧ l ≤ u.length ∧ (n = 1 ∨ n = -1)) ∧
      (∀ u v, YOccurs Ω u → YOccurs Ω v → u ≠ v → Incompatible u v) := by
  sorry

end LodhaMoore
