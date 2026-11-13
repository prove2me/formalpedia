-- Prove2me | Theorems.Thm_HDXHitting_partite_vertex_decomposition
-- name    : HDXHitting.partite_vertex_decomposition
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T17:58:30.625991+00:00
-- url     : https://prove2.me/theorems/33517eb0-cfcd-4d58-a120-576331d7af11
-- title:
--   Proof of Lemma 3.2 (partite) — $\mathbb E\prod f=\mathbb E\prod f_{-v}+h_v\mathbb E_{X_v}\prod f\le c_d(\vec\mu-h_v\vec e_i)+h_vc_{d-1}(\vec\mu_v)$
-- statement:
--   Let $p$ be the top distribution of a $d$-dimensional complex with colouring $c$, colour set $S$, and let $v$ be a vertex of colour $i=c(v)$ with $\pi_1(v)>0$. For a function $f$ put $f_{-v}:=f-f(v)1(v)$ and $h_v:=\pi_{1|\{i\}}(v)f(v)=d\,\pi_1(v)\,f(v)$. Then:
--   1. $$\mathbb E_{\tau\sim\pi_d}\Big[\prod_{w\in\tau}f(w)\Big]=\mathbb E_{\tau\sim\pi_d}\Big[\prod_{w\in\tau}f_{-v}(w)\Big]+h_v\,\mathbb E_{\sigma\sim\pi_{v,d-1}}\Big[\prod_{w\in\sigma}f(w)\Big];$$
--   2. the colour means of $f_{-v}$ are $\vec\mu-h_v\vec e_i$, where $\vec\mu$ are the colour means of $f$ and $\vec e_i$ is the $i$-th coordinate vector;
--   3. consequently, if $f(v)\ge0$ (so $h_v\ge0$), the first expectation is at most $c_d$ of the colour means of $f_{-v}$ and the second is at most $c_{d-1}(\vec\mu_v)$ (the two induction hypotheses), then
--   $$
--   \mathbb E_{\tau\sim\pi_d}\Big[\prod_{w\in\tau}f(w)\Big]\le c_d(\vec\mu-h_v\vec e_i)+h_v\,c_{d-1}(\vec\mu_v),
--   $$
--   where $\vec\mu_v$ are the colour means of $f$ on the link $X_v$ and $c_{d-1}$ is taken over the colours $S\setminus\{i\}$.
--
--   Differences from the source:
--   - encoding: a d-dimensional complex (X, π) given by X and π_d → a top distribution p on Finset V with IsTopDist d p; X(d) = {σ : p σ > 0}; reason: the complex is determined by its top distribution; same instances
--   - generalization: v ∈ supp f of the colour i of maximum mean, f : X(1) → [0, 1], on a d-partite λ-HDX → every vertex v with π_1(v) > 0, its colour i = c(v), every real f in clauses 1–2 and every f with f(v) ≥ 0 in clause 3, every top distribution and colouring; reason: the identity and the mean shift are algebraic, and clause 3 only needs h_v ≥ 0; they specialize to the page's v and f
--   - reading: the two induction hypotheses (on |supp f| and on d) → explicit hypotheses of clause 3; reason: an inductive step stated as an implication
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), proof of Lemma 3.2 (partite bound), pp.16–17

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_hit
import Definitions.Def_HDXHitting_linkDist
import Definitions.Def_HDXHitting_colourMean
import Definitions.Def_HDXHitting_cPoly

namespace HDXHitting

/-- Partite vertex decomposition (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), proof of Lemma 3.2, pp.16–17): for a vertex `v`
of colour `i = c(v)` with `π_1(v) > 0`, `f_{−v} := f − f(v) 1(v)` and
`h_v := π_{1|{i}}(v) f(v) = d π_1(v) f(v)`,
1. `E_{τ∼π_d}[∏_{w∈τ} f(w)] = E_{τ∼π_d}[∏_{w∈τ} f_{−v}(w)] + h_v E_{σ∼π_{v,d−1}}[∏_{w∈σ} f(w)]`;
2. the colour means of `f_{−v}` are `µ⃗ − h_v e⃗_i`;
3. hence, if `f(v) ≥ 0` (so `h_v ≥ 0`; the page's `f` takes values in `[0, 1]`), the first term
   is at most `c_d` of its means and the second expectation at most `c_{d−1}(µ⃗_v)` (the two
   induction hypotheses), then
   `E_{τ∼π_d}[∏_{w∈τ} f(w)] ≤ c_d(µ⃗ − h_v e⃗_i) + h_v c_{d−1}(µ⃗_v)`, where `µ⃗_v` are the colour
   means on the link `X_v` and `c_{d−1}` is taken over the colours `S ∖ {i}`. -/
theorem partite_vertex_decomposition {V ι : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq ι] (d : ℕ) (p : Finset V → ℝ) (hp : IsTopDist d p) (c : V → ι)
    (S : Finset ι) (lam : ℝ) (v : V) (hv : 0 < vertexMeasure d p v) (f : V → ℝ) (h : ℝ)
    (hh : h = (d : ℝ) * vertexMeasure d p v * f v) :
    hit p f = hit p (Function.update f v 0) + h * hit (linkDist p {v}) f ∧
      colourMean p c (Function.update f v 0) = colourMean p c f - h • Pi.single (c v) 1 ∧
      (0 ≤ f v →
        hit p (Function.update f v 0) ≤ cPoly S lam (colourMean p c (Function.update f v 0)) →
        hit (linkDist p {v}) f ≤ cPoly (S.erase (c v)) lam (colourMean (linkDist p {v}) c f) →
        hit p f ≤ cPoly S lam (colourMean p c f - h • Pi.single (c v) 1) +
          h * cPoly (S.erase (c v)) lam (colourMean (linkDist p {v}) c f)) := by sorry

end HDXHitting
