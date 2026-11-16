-- Prove2me | Theorems.Thm_HDXHitting_Supplement_theorem_4_1
-- name    : HDXHitting.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:51:39.821136+00:00
-- url     : https://prove2.me/theorems/5ad42aef-5ddc-4f6e-b18b-1aaa8b319a61
-- title:
--   Theorem 4.1 — hitting-to-concentration: $\Pr[\bar f(\sigma)\ge\varepsilon]\le\frac\mu\varepsilon(B_t/(\varepsilon-\beta_t)_+)^{t-1}$ on two-sided, one-sided and partite HDX
-- statement:
--   Let $1\le k<d$ and let $X$ be a $d$-dimensional complex with top distribution $\pi_d$. Fix $\lambda\ge0$ and $0\le\mu<\varepsilon\le1$, and let $f:X(k)\to[0,1]$ satisfy $\mathbb E_{\pi_k}f\le\mu$. Write $\bar f(\sigma)$ for the uniform average of $f$ over the $k$-subsets of $\sigma$, and set
--   $$
--   \alpha_t:=\max\Big\{\lambda,\frac{1}{d-tk+1}\Big\},\qquad\beta_t:=\frac{(t-1)k}{d-(t-1)k},\qquad C_t:=\exp\Big(\frac{tk^2}{2(d-tk+1)}\Big).
--   $$
--   For every integer $t\ge1$ with $kt<d$ and $\beta_t<\varepsilon$,
--   $$
--   \Pr_{\sigma\sim\pi_d}\big[\bar f(\sigma)\ge\varepsilon\big]\le\frac{\mu}{\varepsilon}\Big(\frac{B_t}{(\varepsilon-\beta_t)_+}\Big)^{t-1},
--   $$
--   where the following choices of $B_t$ are valid:
--   1. $B_t=\mu+tk\lambda$ if $X$ is a $\lambda$-two-sided HDX;
--   2. $B_t=\mu+tk\alpha_t$ if $X$ is a $\lambda$-one-sided HDX;
--   3. $B_t=C_t\mu+tk\lambda$ if $X$ is a $d$-partite $\lambda$-HDX.
--
--   This lifts the hitting-set bounds of Section 3 to Chernoff-type upper tails for the empirical mean of a bounded function over the $k$-faces of a random top face; choosing $t$ gives the paper's Corollaries 4.2 and 4.3.
--
--   **Formalization Note** The three rows form one conjunction of three implications; rows 1 and 2 do not use the colouring data, and row 3 is stated for every colour type, colouring $c$ and colour set $S$ with $|S|=d$. The constants are computed in the reals, and $(x)_+=\max(x,0)$.
--
--   Differences from the source:
--   - encoding: a d-dimensional complex (X, π) → a top distribution p on Finset V with IsTopDist d p (the published base definition); Pr_{σ∼π_d}[f̄(σ) ≥ ε] → the sum of p σ over the vertex sets σ with ε ≤ faceAvg k f σ; reason: the complex is determined by its top distribution and p vanishes off the top faces; same instances
--   - encoding: f : X(k) → [0, 1] → f : Finset V → ℝ with 0 ≤ f τ ≤ 1 for every finite vertex set τ; reason: only the values on k-faces are read (by f̄ on top faces and by π_k), and every f on X(k) extends to all sets with values in [0, 1]
--   - encoding: λ-one-sided, λ-two-sided, d-partite λ-HDX → the published IsOneSidedHDX, the new IsTwoSidedHDX and IsRainbow with |S| = d plus the published IsPartiteHDX, all in Rayleigh form on unnormalized link weights; reason: Courant–Fischer for the self-adjoint link walk, the second singular value is its norm on mean-zero functions, and the walk does not see a scaling of the weights
--   - encoding: β_t := (t − 1)k/(d − (t − 1)k) < ε (printed inside the definition of β_t) → the hypothesis hβ; reason: the printed "< ε" is a standing condition on t; with it (ε − β_t)_+ = ε − β_t
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d9400dc6e1b6e21e0efe05488a4e247d1be3b89a9c202e92f1e3e56d3), Theorem 4.1, pp.20–21 (statement p.20, constants α_t, β_t, C_t p.21)

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXConc_SecondEigLE
import Definitions.Def_HDXHitting_IsOneSidedHDX
import Definitions.Def_HDXHitting_BipSingLE
import Definitions.Def_HDXHitting_IsRainbow
import Definitions.Def_HDXHitting_IsPartiteHDX
import Definitions.Def_HDXHitting_Supplement_IsTwoSidedHDX
import Definitions.Def_HDXHitting_Supplement_faceAvg
import Definitions.Def_HDXHitting_Supplement_kFaceMean

namespace HDXHitting.Supplement

open HDXHitting

/-- Theorem 4.1 (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027
submission manuscript (sha256 60d23b0d…e56d3), pp.20–21), hitting-to-concentration. Let
`1 ≤ k < d`, let `X` be a `d`-dimensional complex with top distribution `p = π_d`, fix `λ ≥ 0`
and `0 ≤ µ < ε ≤ 1`, and let `f : X(k) → [0, 1]` satisfy `E_{π_k} f ≤ µ`. For every integer
`t ≥ 1` with `kt < d` and `β_t < ε`,
`Pr_{σ∼π_d}[f̄(σ) ≥ ε] ≤ (µ/ε) (B_t / (ε − β_t)_+)^{t−1}`, where
1. `B_t = µ + tkλ` if `X` is a `λ`-two-sided HDX;
2. `B_t = µ + tkα_t` if `X` is a `λ`-one-sided HDX;
3. `B_t = C_t µ + tkλ` if `X` is a `d`-partite `λ`-HDX (colouring `c` with `d` colours `S`),
with `α_t = max{λ, 1/(d − tk + 1)}`, `β_t = (t − 1)k/(d − (t − 1)k)`,
`C_t = exp(tk²/(2(d − tk + 1)))`.

**Formalization Note** `Pr_{σ∼π_d}[f̄(σ) ≥ ε]` is `∑_σ p σ` over the sets with
`ε ≤ faceAvg k f σ` (`p` vanishes off the top faces). `f` takes values in `[0, 1]` on every
finite vertex set (any `f : X(k) → [0, 1]` extends so). The constants are computed in `ℝ`
(no `ℕ` subtraction or division); `kt < d` makes every denominator `≥ 1`. `(x)_+` is
`max x 0`. The printed "`β_t := … < ε`" is the hypothesis `hβ`. Rows 1 and 2 do not use the
colouring data `ι, c, S`. -/
theorem theorem_4_1 {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι] (d k : ℕ)
    (hk : 1 ≤ k) (hkd : k < d) (p : Finset V → ℝ) (hp : IsTopDist d p) (lam : ℝ)
    (hlam : 0 ≤ lam) (μ ε : ℝ) (hμ : 0 ≤ μ) (hμε : μ < ε) (hε : ε ≤ 1) (f : Finset V → ℝ)
    (hf : ∀ τ, 0 ≤ f τ ∧ f τ ≤ 1) (hmean : kFaceMean d k p f ≤ μ) (t : ℕ) (ht : 1 ≤ t)
    (hkt : k * t < d) (hβ : ((t : ℝ) - 1) * k / ((d : ℝ) - ((t : ℝ) - 1) * k) < ε)
    (c : V → ι) (S : Finset ι) :
    let α : ℝ := max lam (1 / ((d : ℝ) - t * k + 1))
    let β : ℝ := ((t : ℝ) - 1) * k / ((d : ℝ) - ((t : ℝ) - 1) * k)
    let C : ℝ := Real.exp (t * (k : ℝ) ^ 2 / (2 * ((d : ℝ) - t * k + 1)))
    let tail : ℝ := ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => ε ≤ faceAvg k f σ), p σ
    (IsTwoSidedHDX d p lam →
        tail ≤ μ / ε * ((μ + t * k * lam) / max (ε - β) 0) ^ (t - 1)) ∧
      (IsOneSidedHDX d p lam →
        tail ≤ μ / ε * ((μ + t * k * α) / max (ε - β) 0) ^ (t - 1)) ∧
      (S.card = d → IsRainbow p c S → IsPartiteHDX p c S lam →
        tail ≤ μ / ε * ((C * μ + t * k * lam) / max (ε - β) 0) ^ (t - 1)) := by sorry

end HDXHitting.Supplement
