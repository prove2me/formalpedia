-- Prove2me | Theorems.Thm_HDXHitting_vertex_decomposition
-- name    : HDXHitting.vertex_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:57:41.320889+00:00
-- url     : https://prove2.me/theorems/ba446174-784d-4ebc-8ed9-732dfcfea7e7
-- title:
--   Proof of Lemma 3.2 — vertex decomposition $\mathbb E\prod f=\mathbb E\prod f_\epsilon+d\epsilon\pi(v)\mathbb E_{X_v}\prod f_\epsilon$
-- statement:
--   Let $p$ be the top distribution of a $d$-dimensional complex and $v$ a vertex with $\pi_1(v)>0$. For every function $f$ on the vertices and every $\epsilon\in\mathbb R$, with $f_\epsilon := f-\epsilon\,1(v)$,
--   $$
--   \mathbb E_{\tau\sim\pi_d}\Big[\prod_{w\in\tau}f(w)\Big] = \mathbb E_{\tau\sim\pi_d}\Big[\prod_{w\in\tau}f_\epsilon(w)\Big] + d\,\epsilon\,\pi(v)\,\mathbb E_{\sigma\sim\pi_{v,d-1}}\Big[\prod_{w\in\sigma}f_\epsilon(w)\Big],
--   $$
--   where $\pi_{v,d-1}$ is the top distribution of the link $X_v$.
--
--   This identity is the first step of the derivative bound (4).
--
--   Differences from the source:
--   - encoding: a d-dimensional complex (X, π) given by X and π_d → a top distribution p on Finset V with IsTopDist d p; X(d) = {σ : p σ > 0}; reason: the complex is determined by its top distribution; same instances
--   - generalization: the maximizer f of c_d(µ) and ε small enough (with f(v) > 0) → every real function f and every ε ∈ ℝ; reason: the identity is algebraic in f and ε; it specializes to the page's f and ε
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), proof of Lemma 3.2, p.16

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_hit
import Definitions.Def_HDXHitting_linkDist

namespace HDXHitting

/-- Vertex decomposition (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), proof of Lemma 3.2, p.16): for a `d`-dimensional complex,
a vertex `v` with `π_1(v) > 0`, any `f` and any `ε`, with `f_ε := f − ε 1(v)`,
`E_{τ∼π_d}[∏_{w∈τ} f(w)] = E_{τ∼π_d}[∏_{w∈τ} f_ε(w)] + d ε π(v) E_{σ∼π_{v,d−1}}[∏_{w∈σ} f_ε(w)]`. -/
theorem vertex_decomposition {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (v : V) (hv : 0 < vertexMeasure d p v)
    (f : V → ℝ) (ε : ℝ) :
    hit p f = hit p (Function.update f v (f v - ε)) +
      (d : ℝ) * ε * vertexMeasure d p v * hit (linkDist p {v}) (Function.update f v (f v - ε)) := by sorry

end HDXHitting
