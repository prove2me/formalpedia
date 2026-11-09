-- Prove2me | Theorems.Thm_HDXHitting_eq_3
-- name    : HDXHitting.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:58:55.171817+00:00
-- url     : https://prove2.me/theorems/a20614f6-d999-496d-ac9e-9f3e2f547ec3
-- title:
--   Lemma 3.2 (partite bound), Eq. (3) — $\mathbb E\prod_{v\in\tau}f(v)\le\frac1d\sum_i\mu_i\prod_{j\ne i}(\mu_j+d\lambda)$
-- statement:
--   Let $X$ be a $d$-partite $\lambda$-HDX for some $\lambda\ge0$, with top distribution $\pi_d$, and let $f:X(1)\to[0,1]$. With $\mu_i:=\mathbb E_{\pi_{1|\{i\}}}f$ for each colour $i\in[d]$,
--   $$
--   \mathbb E_{\tau\sim\pi_d}\Big[\prod_{v\in\tau}f(v)\Big]\le\frac1d\sum_{i=1}^d\mu_i\prod_{j\ne i}(\mu_j+d\lambda). \tag{3}
--   $$
--   This finer bound handles unequal means in different colour classes; with all $\mu_i$ equal to $\mu$ it gives $\mu(\mu+d\lambda)^{d-1}$.
--
--   Differences from the source:
--   - encoding: a d-dimensional complex (X, π) given by X and π_d → a top distribution p on Finset V with IsTopDist d p; X(d) = {σ : p σ > 0}; reason: the complex is determined by its top distribution; same instances
--   - encoding: f : X(1) → [0, 1] → f : V → ℝ with 0 ≤ f v ≤ 1 for every v of the finite vertex type V; reason: values off X(1) carry no weight and are never read
--   - reading: a d-dimensional complex → 1 ≤ d; reason: the paper's complexes have d ≥ 1 (its induction starts at d = 1); at d = 0 the printed bound fails (hit 1, mean 0)
--   - encoding: X d-partite with parts A_1, …, A_d and µ_i = E_{π_{1|{i}}} f → a colouring c : V → ι with a colour set S, |S| = d, IsRainbow p c S, and colourMean; reason: A_i = c⁻¹(i); a d-face meeting each part at most once meets each exactly once
--   - encoding: second singular value of each colour-pair link graph at most λ → IsPartiteHDX: the Rayleigh-form BipSingLE on the colour-(i, j) link weights; reason: the second singular value is the walk's norm on mean-zero functions; λ ≥ 0
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Lemma 3.2, Eq. (3), p.15

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_hit
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXHitting_BipSingLE
import Definitions.Def_HDXHitting_IsPartiteHDX
import Definitions.Def_HDXHitting_IsRainbow
import Definitions.Def_HDXHitting_colourMean
import Definitions.Def_HDXHitting_cPoly

namespace HDXHitting

/-- Lemma 3.2, partite bound, Eq. (3) (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), p.15): if `X` is a `d`-partite `λ`-HDX
(`λ ≥ 0`) and `f : X(1) → [0, 1]`, with `µ_i := E_{π_{1|{i}}} f` for `i ∈ [d]`,
`E_{τ∼π_d}[∏_{v∈τ} f(v)] ≤ (1/d) ∑_{i=1}^{d} µ_i ∏_{j≠i} (µ_j + dλ)`.

**Formalization Note** The `d` colours are a set `S` with `|S| = d ≥ 1` in an arbitrary colour
type; `IsRainbow p c S` is `d`-partiteness. -/
theorem eq_3 {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι] (d : ℕ) (hd : 1 ≤ d)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (c : V → ι) (S : Finset ι) (hS : S.card = d)
    (hc : IsRainbow p c S) (lam : ℝ) (hlam : 0 ≤ lam) (hX : IsPartiteHDX p c S lam)
    (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    hit p f ≤ cPoly S lam (colourMean p c f) := by sorry

end HDXHitting
