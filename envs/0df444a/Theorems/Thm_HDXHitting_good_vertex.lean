-- Prove2me | Theorems.Thm_HDXHitting_good_vertex
-- name    : HDXHitting.good_vertex
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T17:59:03.679486+00:00
-- url     : https://prove2.me/theorems/4f207efc-12cc-43ec-8fe1-c340250d66e9
-- title:
--   Proof of Lemma 3.2 — a vertex $v$ with $f(v)>0$ and $\mu_v\le\mu+\lambda$
-- statement:
--   Let $p$ be the top distribution of a $d$-dimensional $\lambda$-one-sided HDX with $d\ge2$ and $\lambda\ge0$, and let $f:V\to[0,1]$ have mean $\mu>0$. Then there is a vertex $v$ of the complex ($\pi_1(v)>0$) with $f(v)>0$ and
--   $$
--   \mu_v := \mathbb E_{w\sim X_v(1)} f(w) \le \mu+\lambda ,
--   $$
--   where $\mu_v$ is the mean of $f$ under the vertex distribution of the link $X_v$.
--
--   Differences from the source:
--   - encoding: a d-dimensional complex (X, π) given by X and π_d → a top distribution p on Finset V with IsTopDist d p; X(d) = {σ : p σ > 0}; reason: the complex is determined by its top distribution; same instances
--   - encoding: f : X(1) → [0, 1] → f : V → ℝ with 0 ≤ f v ≤ 1 for every v of the finite vertex type V; reason: values off X(1) carry no weight and are never read
--   - encoding: second eigenvalue of every link graph at most λ → IsOneSidedHDX: the published Rayleigh-form HDXConc.SecondEigLE on unnormalized link weights for every τ with |τ| + 2 ≤ d; reason: Courant–Fischer for the self-adjoint walk; scale invariance
--   - generalization: f the maximizer of c_d(µ) for µ ∈ (0, 1) → every f : V → [0, 1] with mean µ > 0; reason: the page's argument uses only f ∈ [0, 1] and µ > 0
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), proof of Lemma 3.2, p.16 ("It remains to justify the existence a v such that µ_v ≤ µ + λ")

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_mean
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXConc_SecondEigLE
import Definitions.Def_HDXHitting_IsOneSidedHDX
import Definitions.Def_HDXHitting_linkDist

namespace HDXHitting

/-- Existence of a good vertex (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), proof of Lemma 3.2, p.16): on a `d`-dimensional
`λ`-one-sided HDX with `d ≥ 2` and `λ ≥ 0`, every `f : V → [0, 1]` with mean `µ > 0` has a vertex
`v` (with `π_1(v) > 0`) such that `f(v) > 0` and `µ_v := E_{w∼X_v(1)} f(w) ≤ µ + λ`, where `µ_v` is
the mean of `f` under the vertex distribution of the link `X_v`. -/
theorem good_vertex {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd : 2 ≤ d)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX : IsOneSidedHDX d p lam) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1)
    (hμ : 0 < mean d p f) :
    ∃ v, 0 < f v ∧ 0 < vertexMeasure d p v ∧
      mean (d - 1) (linkDist p {v}) f ≤ mean d p f + lam := by sorry

end HDXHitting
