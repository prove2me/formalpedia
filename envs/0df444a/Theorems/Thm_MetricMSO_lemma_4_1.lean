-- Prove2me | Theorems.Thm_MetricMSO_lemma_4_1
-- name    : MetricMSO.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:09.606213+00:00
-- url     : https://prove2.me/theorems/60b6972d-07b2-40c9-a6c7-76dcc3fea361
-- title:
--   Lemma 4.1 — equal arc lengths iff an integer potential on the cycle
-- statement:
--   Let $G[C]$ be a cycle, $P$ an $s$-$t$ arc and $Q$ a $u$-$v$ arc of $C$. The arcs have equal lengths if and only if there are $\eta\in\{+,-\}$ and a map $q:C\to\mathbb Z$ such that
--   $$q(z)-q(r)=\beta^\eta_{P,Q}(r,z)\quad\text{for every oriented edge }(r,z)\text{ of }G[C].$$
--   If the lengths agree, $\eta$ and $q$ can be chosen so that $q$ is $1$-Lipschitz on $G[C]$.
--
--   Differences from the source:
--   - encoding: a map q : C → ℤ → a map on V of which only the values on C are used; reason: restriction and arbitrary extension are inverse
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), Lemma 4.1, p.25 (PDF 27)

import Mathlib
import Definitions.Def_MetricMSO_EqGC
import Definitions.Def_MetricMSO_arcBeta

namespace MetricMSO

/-- **Lemma 4.1.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.25 (PDF 27), in the setting of §4.1 (`C` a
vertex set with `G[C]` a cycle, `P` an s-t arc and `Q` a u-v arc): "The arcs P and Q have equal lengths
if and only if there exist η ∈ {+, −} and a map q: C → Z such that q(z) − q(r) = β^η_{P,Q}(r, z) for
every oriented edge (r, z) of G[C]. (6) If the lengths agree, we can choose η and q so that q is
1-Lipschitz on G[C]."

**Formalization Note** The map `q : C → ℤ` is a function on `V` of which only the values on `C` are
used. An oriented edge of `G[C]` is an ordered pair of adjacent vertices of `C`. `η = true` is `+`. The
second sentence is the second conjunct. -/
theorem lemma_4_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (C : Finset V)
    (hC : IsCycleSet G C) {s t u v : V} (P : G.Walk s t) (Q : G.Walk u v)
    (hP : IsArc C P) (hQ : IsArc C Q) :
    (P.length = Q.length ↔ ∃ (η : Bool) (q : V → ℤ), ∀ r ∈ C, ∀ z ∈ C, G.Adj r z →
      q z - q r = arcBeta η P Q r z) ∧
    (P.length = Q.length → ∃ (η : Bool) (q : V → ℤ), (∀ r ∈ C, ∀ z ∈ C, G.Adj r z →
      q z - q r = arcBeta η P Q r z) ∧ ∀ r ∈ C, ∀ z ∈ C, G.Adj r z → |q z - q r| ≤ 1) := by sorry

end MetricMSO
