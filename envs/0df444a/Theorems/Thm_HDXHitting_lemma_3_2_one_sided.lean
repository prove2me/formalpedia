-- Prove2me | Theorems.Thm_HDXHitting_lemma_3_2_one_sided
-- name    : HDXHitting.lemma_3_2_one_sided
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T17:59:00.999437+00:00
-- url     : https://prove2.me/theorems/2f3585a2-dd13-4119-b971-0cb4ab70c545
-- title:
--   Lemma 3.2 (one-sided bound) — $\mathbb E_{\tau\sim\pi_d}\prod_{v\in\tau}f(v)\le\mu(\mu+d\lambda)^{d-1}$
-- statement:
--   Let $X$ be a $d$-dimensional $\lambda$-one-sided HDX for some $\lambda\ge0$, with top distribution $\pi_d$, and let $f:X(1)\to[0,1]$ have mean $\mathbb E_\pi f=\mu$. Then
--   $$
--   \mathbb E_{\tau\sim\pi_d}\Big[\prod_{v\in\tau}f(v)\Big]\le\mu(\mu+d\lambda)^{d-1}.
--   $$
--   For $f=1_S$ this bounds the probability that a random top face lies inside $S$ by $\mu(\mu+d\lambda)^{d-1}$, the analogue of the expander hitting set lemma for high-dimensional expanders.
--
--   Differences from the source:
--   - encoding: a d-dimensional complex (X, π) given by X and π_d → a top distribution p on Finset V with IsTopDist d p; X(d) = {σ : p σ > 0}; reason: the complex is determined by its top distribution; same instances
--   - encoding: f : X(1) → [0, 1] → f : V → ℝ with 0 ≤ f v ≤ 1 for every v of the finite vertex type V; reason: values off X(1) carry no weight and are never read
--   - reading: a d-dimensional complex → 1 ≤ d; reason: the paper's complexes have d ≥ 1 (its induction starts at d = 1); at d = 0 the printed bound fails (hit 1, mean 0)
--   - encoding: second eigenvalue of every link graph at most λ → IsOneSidedHDX: the published Rayleigh-form HDXConc.SecondEigLE on unnormalized link weights for every τ with |τ| + 2 ≤ d; reason: Courant–Fischer for the self-adjoint walk; scale invariance
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

namespace HDXHitting

/-- Lemma 3.2, one-sided bound (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), p.15): let `X` be a `d`-dimensional `λ`-one-sided
HDX for some `λ ≥ 0`, and `f : X(1) → [0, 1]` with mean `E_π f = µ`. Then
`E_{τ∼π_d}[∏_{v∈τ} f(v)] ≤ µ(µ + dλ)^{d−1}`.

**Formalization Note** The complex is given by its top distribution `p` (`IsTopDist d p`),
`1 ≤ d`, and `f` is defined on the whole vertex type with values in `[0, 1]`. -/
theorem lemma_3_2_one_sided {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd : 1 ≤ d)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX : IsOneSidedHDX d p lam) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    hit p f ≤ mean d p f * (mean d p f + d * lam) ^ (d - 1) := by sorry

end HDXHitting
