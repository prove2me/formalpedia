-- Prove2me | Theorems.Thm_HDXHitting_lemma_3_2
-- name    : HDXHitting.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:58:53.311371+00:00
-- url     : https://prove2.me/theorems/4902865c-3b0a-4e3e-8638-5ce427fbce46
-- title:
--   Lemma 3.2 — hitting set bounds $\mu(\mu+d\lambda)^{d-1}$ (one-sided HDX) and Eq. (3) (partite HDX)
-- statement:
--   Let $X$ be a $d$-dimensional complex with top distribution $\pi_d$, let $\lambda\ge0$, and let $f:X(1)\to[0,1]$ have mean $\mu=\mathbb E_\pi f$.
--   1. If $X$ is a $\lambda$-one-sided HDX, then
--   $$
--   \mathbb E_{\tau\sim\pi_d}\Big[\prod_{v\in\tau}f(v)\Big]\le\mu(\mu+d\lambda)^{d-1}.
--   $$
--   2. If $X$ is a $d$-partite $\lambda$-HDX, then with $\mu_i:=\mathbb E_{\pi_{1|\{i\}}}f$ for each colour $i\in[d]$,
--   $$
--   \mathbb E_{\tau\sim\pi_d}\Big[\prod_{v\in\tau}f(v)\Big]\le\frac1d\sum_{i=1}^d\mu_i\prod_{j\ne i}(\mu_j+d\lambda). \tag{3}
--   $$
--   For $f=1_S$ the first clause says a random top face lies inside a set of density $\mu$ with probability at most $\mu(\mu+d\lambda)^{d-1}$, the high-dimensional analogue of the expander hitting set lemma; the paper builds its sampling results on it.
--
--   **Formalization Note** The colouring data of clause 2 (a colour type, a colouring $c$ and a colour set $S$ with $|S|=d$) are universally quantified; clause 1 does not use them, and clause 2 does not assume clause 1's hypothesis.
--
--   Differences from the source:
--   - encoding: a d-dimensional complex (X, π) given by X and π_d → a top distribution p on Finset V with IsTopDist d p; X(d) = {σ : p σ > 0}; reason: the complex is determined by its top distribution; same instances
--   - encoding: f : X(1) → [0, 1] → f : V → ℝ with 0 ≤ f v ≤ 1 for every v of the finite vertex type V; reason: values off X(1) carry no weight and are never read
--   - reading: a d-dimensional complex → 1 ≤ d; reason: the paper's complexes have d ≥ 1 (its induction starts at d = 1); at d = 0 the printed bound fails (hit 1, mean 0)
--   - encoding: second eigenvalue of every link graph at most λ → IsOneSidedHDX: the published Rayleigh-form HDXConc.SecondEigLE on unnormalized link weights for every τ with |τ| + 2 ≤ d; reason: Courant–Fischer for the self-adjoint walk; scale invariance
--   - encoding: X d-partite with parts A_1, …, A_d and µ_i = E_{π_{1|{i}}} f → a colouring c : V → ι with a colour set S, |S| = d, IsRainbow p c S, and colourMean; reason: A_i = c⁻¹(i); a d-face meeting each part at most once meets each exactly once
--   - encoding: second singular value of each colour-pair link graph at most λ → IsPartiteHDX: the Rayleigh-form BipSingLE on the colour-(i, j) link weights; reason: the second singular value is the walk's norm on mean-zero functions; λ ≥ 0
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Lemma 3.2, p.15

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_mean
import Definitions.Def_HDXHitting_hit
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXConc_SecondEigLE
import Definitions.Def_HDXHitting_IsOneSidedHDX
import Definitions.Def_HDXHitting_IsRainbow
import Definitions.Def_HDXHitting_BipSingLE
import Definitions.Def_HDXHitting_IsPartiteHDX
import Definitions.Def_HDXHitting_colourMean
import Definitions.Def_HDXHitting_cPoly

namespace HDXHitting

/-- Lemma 3.2 (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), p.15), both clauses. Let `X` be a `d`-dimensional complex (`d ≥ 1`)
with top distribution `π_d`, let `λ ≥ 0`, and let `f : X(1) → [0, 1]` with mean `E_π f = µ`.
1. If `X` is a `λ`-one-sided HDX, then `E_{τ∼π_d}[∏_{v∈τ} f(v)] ≤ µ(µ + dλ)^{d−1}`.
2. If `X` is a `d`-partite `λ`-HDX (colouring `c` with `d` colours `S`), then with
   `µ_i := E_{π_{1|{i}}} f`,
   `E_{τ∼π_d}[∏_{v∈τ} f(v)] ≤ (1/d) ∑_{i∈S} µ_i ∏_{j∈S, j≠i} (µ_j + dλ)` (Eq. (3)).

**Formalization Note** Clause 1 does not depend on the colouring data `ι, c, S`; clause 2
assumes only partiteness and the partite HDX condition, not clause 1's hypothesis. -/
theorem lemma_3_2 {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι] (d : ℕ)
    (hd : 1 ≤ d) (p : Finset V → ℝ) (hp : IsTopDist d p) (lam : ℝ) (hlam : 0 ≤ lam)
    (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) (c : V → ι) (S : Finset ι) :
    (IsOneSidedHDX d p lam → hit p f ≤ mean d p f * (mean d p f + d * lam) ^ (d - 1)) ∧
      (S.card = d → IsRainbow p c S → IsPartiteHDX p c S lam →
        hit p f ≤ cPoly S lam (colourMean p c f)) := by sorry

end HDXHitting
