-- Prove2me | Theorems.Thm_GeoSemialgCSP_lemma_4_2
-- name    : GeoSemialgCSP.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:32.927695+00:00
-- url     : https://prove2.me/theorems/514b19a3-312e-43a2-9b2d-c5fc6b0b7f2c
-- title:
--   Lemma 4.2 — uniform random embeddings
-- statement:
--   Let $k\ge2$, $m=k^h$ and $\varepsilon_L>0$. There are a power $M=k^H$ of $k$ and a finitely supported random map $L_{m,M}:[m]\to[M]$ from the leaves of $T_m$ to the leaves of $T_M$ such that
--
--   1. every realization of $L_{m,M}$ is injective;
--   2. for every $a\in[m]$, $L_{m,M}(a)$ is uniform on $[M]$;
--   3. if $a_1,\dots,a_k$ are cousins in $T_m$, then $\Pr\bigl(\mathrm{cousins}(L_{m,M}(a_1),\dots,L_{m,M}(a_k))=1\text{ in }T_M\bigr)\ge1-\varepsilon_L$.
--
--   The map embeds the multiscale instance into a larger domain so that every variable position is uniform and the variables of each constraint stay distinct.
--
--   Differences from the source:
--   - encoding: leaves of T_m and of T_M numbered 0, …, m−1 and 0, …, M−1 with M = k^H → words Fin h → Fin k and Fin H → Fin k; reason: a leaf's number is the base-k value of its word
--   - encoding: a finitely supported random map L_{m,M} : [m] → [M] → a PMF on the finite type of maps between the leaf sets; reason: every law on a finite type is finitely supported
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.2, pp.10–11 (PDF pp.11–12)

import Mathlib
import Definitions.Def_GeoSemialgCSP_RE1
import Definitions.Def_GeoSemialgCSP_RE2
import Definitions.Def_GeoSemialgCSP_RE3

namespace GeoSemialgCSP

/-- **Lemma 4.2 (uniform random embeddings).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.2, printed pp.10–11 (PDF pp.11–12):
for `m = k^h` and `ε_L > 0` there are a power `M = k^H` of `k` and a finitely supported random map
`L_{m,M} : [m] → [M]` such that (1) every realization is injective, (2) each `L_{m,M}(a)` is
uniform on `[M]`, and (3) cousins tuples of `T_m` are mapped to cousins tuples of `T_M` with
probability at least `1 − ε_L`. -/
theorem lemma_4_2 {k : ℕ} (hk : 2 ≤ k) (h : ℕ) (εL : ℝ) (hεL : 0 < εL) :
    ∃ (H : ℕ) (L : PMF ((Fin h → Fin k) → Wd k H)), RE1 L ∧ RE2 L ∧ RE3 L εL := by sorry

end GeoSemialgCSP
