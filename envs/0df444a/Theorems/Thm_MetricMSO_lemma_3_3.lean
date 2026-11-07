-- Prove2me | Theorems.Thm_MetricMSO_lemma_3_3
-- name    : MetricMSO.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:54.48042+00:00
-- url     : https://prove2.me/theorems/d3fdf05f-6a46-4463-a9fb-362fecf26d4f
-- title:
--   Lemma 3.3 — vanishing signed sums on a binary cycle basis give a potential
-- statement:
--   Fix a reference orientation of every edge of $G$ and a function $\delta:E(G)\to\mathbb Z$. If the signed sum of $\delta$ around every cycle of a binary cycle basis is zero, then there is a map $\lambda:V(G)\to\mathbb Z$ with
--   $$\lambda(v)-\lambda(u)=\delta(e)$$
--   for every edge $e$ whose reference orientation is $u\to v$. Consequently, the signed sum of $\delta$ around every closed walk is zero.
--
--   Vanishing on a basis over $\mathbb F_2$ is thus enough for an integer potential, although the basis is not a basis of the signed cycle space a priori.
--
--   Differences from the source:
--   - encoding: δ : E(G) → ℤ → δ : Sym2 V → ℤ, of which only the values on edges are used; reason: values off the edges never enter the statement
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), Lemma 3.3, p.21 (PDF 23)

import Mathlib
import Definitions.Def_MetricMSO_cbl
import Definitions.Def_MetricMSO_signedSum

namespace MetricMSO

/-- **Lemma 3.3.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.21 (PDF 23): "Fix a reference orientation
of every edge of G and a function δ: E(G) → Z. If the signed sum of δ around every cycle of a binary
cycle basis B is zero, then there exists a map λ: V(G) → Z such that λ(v) − λ(u) = δ(e) for every
edge e whose reference orientation is u → v. Consequently, the signed sum of δ around every closed
walk is zero."

**Formalization Note** `O u v` says that the reference orientation of the edge `uv` is `u → v`. The
statement quantifies over every orientation `O`. `δ` is a function on `Sym2 V`, of which only the
values on edges matter. -/
theorem lemma_3_3 {V : Type} [Fintype V] (G : SimpleGraph V) (O : V → V → Prop)
    (hO : IsRefOrientation G O) (δ : Sym2 V → ℤ) {k : ℕ} (B : Fin k → CycleOf G)
    (hB : IsCycleBasis B) (h0 : ∀ i, signedSum O δ (B i).walk = 0) :
    (∃ lam : V → ℤ, ∀ u v, O u v → lam v - lam u = δ s(u, v)) ∧
      ∀ (v : V) (W : G.Walk v v), signedSum O δ W = 0 := by sorry

end MetricMSO
