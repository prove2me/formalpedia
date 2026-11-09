-- Prove2me | Theorems.Thm_HDXHitting_cmax_lipschitz
-- name    : HDXHitting.cmax_lipschitz
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:59:15.132956+00:00
-- url     : https://prove2.me/theorems/f1f7478d-545d-4b02-a470-c6273568aa15
-- title:
--   Proof of Lemma 3.2 — $c_d$ is attained and $d$-Lipschitz
-- statement:
--   Let $p$ be the top distribution of a $d$-dimensional complex, $d\ge1$, and let $c_d(\mu)$ be the largest value of $\mathbb E_{\tau\sim\pi_d}[\prod_{v\in\tau}f(v)]$ over $f:V\to[0,1]$ with mean $\mu$. Then:
--   1. for every $\mu\in[0,1]$ the supremum is attained by some $f:V\to[0,1]$ with mean $\mu$;
--   2. for all $\mu,\mu'\in[0,1]$,
--   $$
--   |c_d(\mu)-c_d(\mu')|\le d\,|\mu-\mu'| ;
--   $$
--   in particular $c_d$ is continuous.
--
--   These regularity properties let the proof integrate the derivative bound (4) from $c_d(0)=0$.
--
--   Differences from the source:
--   - encoding: a d-dimensional complex (X, π) given by X and π_d → a top distribution p on Finset V with IsTopDist d p; X(d) = {σ : p σ > 0}; reason: the complex is determined by its top distribution; same instances
--   - encoding: f : X(1) → [0, 1] → f : V → ℝ with 0 ≤ f v ≤ 1 for every v of the finite vertex type V; reason: values off X(1) carry no weight and are never read
--   - reading: a d-dimensional complex → 1 ≤ d; reason: the paper's complexes have d ≥ 1 (its induction starts at d = 1); at d = 0 the printed bound fails (hit 1, mean 0)
--   - encoding: c_d as a function of µ → cMax d p µ for µ ∈ [0, 1]; reason: means of [0, 1]-valued functions lie in [0, 1]; c_d is not defined outside
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), proof of Lemma 3.2, pp.15–16 ("The maximizer f := f_µ exists … c_d is continuous and d-Lipschitz")

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_mean
import Definitions.Def_HDXHitting_hit
import Definitions.Def_HDXHitting_cMax

namespace HDXHitting

/-- `c_d` is attained and `d`-Lipschitz (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), proof of Lemma 3.2, pp.15–16: "The
maximizer `f := f_µ` exists for every `µ` by compactness of the domain, and as a function of
`µ`, `c_d` is continuous and `d`-Lipschitz"): for a `d`-dimensional complex (`d ≥ 1`),
1. for every `µ ∈ [0, 1]` some `f : V → [0, 1]` with mean `µ` attains `c_d(µ)`;
2. `|c_d(µ) − c_d(µ')| ≤ d |µ − µ'|` for all `µ, µ' ∈ [0, 1]` (hence `c_d` is continuous). -/
theorem cmax_lipschitz {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd : 1 ≤ d)
    (p : Finset V → ℝ) (hp : IsTopDist d p) :
    (∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → ∃ f : V → ℝ, (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧ mean d p f = μ ∧
        hit p f = cMax d p μ) ∧
      (∀ μ μ' : ℝ, 0 ≤ μ → μ ≤ 1 → 0 ≤ μ' → μ' ≤ 1 →
        |cMax d p μ - cMax d p μ'| ≤ d * |μ - μ'|) := by sorry

end HDXHitting
