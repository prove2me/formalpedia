-- Prove2me | Theorems.Thm_HDXHitting_partite_good_vertex
-- name    : HDXHitting.partite_good_vertex
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T17:58:48.620121+00:00
-- url     : https://prove2.me/theorems/5fca238e-0950-48d2-a4ae-029808662ee5
-- title:
--   Proof of Lemma 3.2 (partite) — $\mathbb E_{\tilde\pi}(\vec\mu_v)_j\le\mu_j+\lambda\sqrt{\mu_j/\mu_i}$ and a vertex with $c_{d-1}(\vec\mu_v)\le c_{d-1}(\vec\mu_{-i}+\lambda\mathbf 1)$
-- statement:
--   Let $p$ be the top distribution of a $d$-partite $\lambda$-HDX with colouring $c$ and colour set $S$, $|S|=d\ge2$, $\lambda\ge0$, and let $f:V\to[0,1]$ have colour means $\vec\mu$. Let $i\in S$ be a colour of maximum mean, with $\mu_i>0$, and let $\tilde\pi(v)=\pi_{1|\{i\}}(v)f(v)/\mu_i$ on the vertices of colour $i$. Then:
--   1. for every colour $j\ne i$ in $S$,
--   $$
--   \mathbb E_{v\sim\tilde\pi}(\vec\mu_v)_j\le\mu_j+\lambda\sqrt{\mu_j/\mu_i}\le\mu_j+\lambda ,
--   $$
--   where $(\vec\mu_v)_j$ is the colour-$j$ mean of $f$ on the link $X_v$;
--   2. there is a vertex $v\in\operatorname{supp}f$ of colour $i$ (with $\pi_1(v)>0$) such that
--   $$
--   c_{d-1}(\vec\mu_v)\le c_{d-1}(\vec\mu_{-i}+\lambda\mathbf 1),
--   $$
--   with $c_{d-1}$ the polynomial of (3) over the colours $S\setminus\{i\}$.
--
--   Differences from the source:
--   - encoding: a d-dimensional complex (X, π) given by X and π_d → a top distribution p on Finset V with IsTopDist d p; X(d) = {σ : p σ > 0}; reason: the complex is determined by its top distribution; same instances
--   - encoding: f : X(1) → [0, 1] → f : V → ℝ with 0 ≤ f v ≤ 1 for every v of the finite vertex type V; reason: values off X(1) carry no weight and are never read
--   - encoding: X d-partite with parts A_1, …, A_d and µ_i = E_{π_{1|{i}}} f → a colouring c : V → ι with a colour set S, |S| = d, IsRainbow p c S, and colourMean; reason: A_i = c⁻¹(i); a d-face meeting each part at most once meets each exactly once
--   - encoding: second singular value of each colour-pair link graph at most λ → IsPartiteHDX: the Rayleigh-form BipSingLE on the colour-(i, j) link weights; reason: the second singular value is the walk's norm on mean-zero functions; λ ≥ 0
--   - encoding: E_{v∼π̃} → the explicit sum over colour-i vertices with weights d π_1(v) f(v)/µ_i; reason: π_{1|{i}}(v) = d π_1(v) = Pr[v ∈ σ]; same quantity
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), proof of Lemma 3.2 (partite bound), p.17

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXHitting_BipSingLE
import Definitions.Def_HDXHitting_IsPartiteHDX
import Definitions.Def_HDXHitting_linkDist
import Definitions.Def_HDXHitting_IsRainbow
import Definitions.Def_HDXHitting_colourMean
import Definitions.Def_HDXHitting_cPoly

namespace HDXHitting

/-- Existence of a good vertex in the partite case (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), proof of Lemma 3.2, p.17): on a
`d`-partite `λ`-HDX (`d = |S| ≥ 2`, `λ ≥ 0`), for `f : V → [0, 1]` and a colour `i ∈ S` of
maximum mean `µ_i > 0`, with `π̃(v) = π_{1|{i}}(v) f(v)/µ_i` on the colour-`i` vertices,
1. for every colour `j ≠ i` in `S`, `E_{v∼π̃}(µ⃗_v)_j ≤ µ_j + λ√(µ_j/µ_i) ≤ µ_j + λ`;
2. some vertex `v ∈ supp f` of colour `i` (with `π_1(v) > 0`) has
   `c_{d−1}(µ⃗_v) ≤ c_{d−1}(µ⃗_{−i} + λ1)`, where `µ⃗_v` are the colour means on the link `X_v` and
   `c_{d−1}` is over `S ∖ {i}`. -/
theorem partite_good_vertex {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (d : ℕ) (p : Finset V → ℝ) (hp : IsTopDist d p) (c : V → ι) (S : Finset ι)
    (hS : S.card = d) (hd : 2 ≤ d) (hc : IsRainbow p c S) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX : IsPartiteHDX p c S lam) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) (i : ι)
    (hi : i ∈ S) (hmax : ∀ j ∈ S, colourMean p c f j ≤ colourMean p c f i)
    (hpos : 0 < colourMean p c f i) :
    (∀ j ∈ S.erase i,
      ∑ v ∈ Finset.univ.filter (fun v => c v = i),
          ((d : ℝ) * vertexMeasure d p v * f v / colourMean p c f i) *
            colourMean (linkDist p {v}) c f j ≤
        colourMean p c f j + lam * Real.sqrt (colourMean p c f j / colourMean p c f i) ∧
      colourMean p c f j + lam * Real.sqrt (colourMean p c f j / colourMean p c f i) ≤
        colourMean p c f j + lam) ∧
    ∃ v, c v = i ∧ 0 < f v ∧ 0 < vertexMeasure d p v ∧
      cPoly (S.erase i) lam (colourMean (linkDist p {v}) c f) ≤
        cPoly (S.erase i) lam (fun j => colourMean p c f j + lam) := by sorry

end HDXHitting
