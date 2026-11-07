-- Prove2me | Theorems.Thm_LowTempGlauber_lemma_8
-- name    : LowTempGlauber.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:13.642611+00:00
-- url     : https://prove2.me/theorems/7389cca0-92cc-4252-afcc-23b99cb6d3e5
-- title:
--   Lemma 8 — cutwidth $\le d\lceil\log_2\ell\rceil+r$ for connected graphs of tree excess $\le r$
-- statement:
--   Let $C$ be a connected graph on $\ell$ vertices with maximum degree at most $d$ and tree excess $\operatorname{exc}(C)=|E(C)|-|V(C)|+1\le r$. Then there is an ordering $v_1,\dots,v_\ell$ of its vertices such that for every $i$ the number of edges between $\{v_1,\dots,v_i\}$ and the remaining vertices is at most
--   $$d\lceil\log_2\ell\rceil+r.$$
--
--   The ordering fixes the sweep order of the component switch (Definition 9), and the cut bound is what limits the number of vertices the canonical-path encoding in Lemma 10 has to delete.
--
--   Differences from the source:
--   - encoding: an ordering v₁, …, v_ℓ, the cut induced by v₁, …, v_i, ⌈log₂ ℓ⌉ → a bijection e : Fin ℓ ≃ V, the number of adjacent ordered pairs (u, w) with u among the first i and w not (each cut edge once), for i ≤ ℓ, and Nat.clog 2 ℓ; reason: same quantities; for i > ℓ the cut is empty; r a natural number loses nothing since exc(C) is an integer
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Lemma 8, p.10 (proof in Appendix A, p.60)

import Mathlib

open Classical

namespace LowTempGlauber

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…), Lemma 8, p.10 (proof in Appendix A, p.60).

If `C` is a connected graph on `ℓ` vertices with maximum degree at most `d` and tree excess
`exc(C) = |E(C)| − |V(C)| + 1 ≤ r`, there is an ordering `v₁, …, v_ℓ` of its vertices such that for
every `i` the cut between `{v₁, …, v_i}` and the other vertices has at most `d⌈log₂ ℓ⌉ + r` edges.

**Formalization Note.** The ordering is `e : Fin ℓ ≃ V` (`v_{j+1} = e j`); the cut after `i` vertices
counts adjacent pairs `(u, w)` with `u` among the first `i` and `w` not, each edge once.
`⌈log₂ ℓ⌉` is `Nat.clog 2 ℓ`. -/
theorem lemma_8 {V : Type*} [Fintype V] (C : SimpleGraph V) (ℓ d r : ℕ)
    (hcard : Fintype.card V = ℓ) (hconn : C.Connected) (hdeg : ∀ v, C.degree v ≤ d)
    (hexc : (C.edgeFinset.card : ℤ) - ℓ + 1 ≤ r) :
    ∃ e : Fin ℓ ≃ V, ∀ i ≤ ℓ,
      ((Finset.univ ×ˢ Finset.univ).filter (fun p : V × V =>
          C.Adj p.1 p.2 ∧ ((e.symm p.1 : ℕ) < i) ∧ ¬ ((e.symm p.2 : ℕ) < i))).card ≤
        d * Nat.clog 2 ℓ + r := by sorry

end LowTempGlauber
