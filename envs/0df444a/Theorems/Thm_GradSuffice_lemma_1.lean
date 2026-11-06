-- Prove2me | Theorems.Thm_GradSuffice_lemma_1
-- name    : GradSuffice.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:50.086474+00:00
-- url     : https://prove2.me/theorems/7da7745c-b994-43f2-bdaa-2cb366470038
-- title:
--   Lemma 1, p.21 — under (12), $f=f_{t,k}$, $\bar f=\bar f_{t,k}$ and $\nabla\bar f=\nabla\bar f_{t,k}$
-- statement:
--   Consider the hard instance of Theorem 8: a margin $0<\theta<1$, a convex symmetric set $W\subseteq B$, a $B^\star$-valued tree $\bar\xi$ of depth $DL$, branches $\sigma_1,\dots,\sigma_\kappa$ with witnesses $w_{\sigma_k}\in W$ realizing them at margin $\theta$, a session length $D\ge1$ and a noise level $0<\nu\le\theta/(512D)$. Let $f$, $f_{t,k}$ be the noisy hard function and its truncations, and $\bar f$, $\bar f_{t,k}$ their averages over the uniform noise on $[-\nu,\nu]$.
--
--   **Lemma 1.** If $w$ satisfies condition (12) for $t$ and $k$, that is $|\eta_{u,k}\cdot y_k(w)|\le\frac{\theta}{128D}\mu_k(w)$ for $t\le u\le D$, then for every realization of the noise
--   $$f(w)=f_{t,k}(w),$$
--   and consequently $\bar f(w)=\bar f_{t,k}(w)$ and $\nabla\bar f(w)=\nabla\bar f_{t,k}(w)$.
--
--   The lemma says that a query satisfying (12) reveals only the part of the function that depends on the first $k-1$ branches and the first $t$ blocks of the $k$-th branch; it is the basis of the session argument in the proof of Theorem 8.
--
--   **Formalization Note** Indices $t$, $k$ are 0-based; a noise realization is any assignment of values in $[-\nu,\nu]$ to the noise variables, and $\nabla$ is the Fréchet derivative.
--
--   Differences from the source:
--   - generalization: D := ⌊(θ²m/(65536 log(16m²)))^{1/3}⌋ for the depth m of the shattered tree, which is cut to depth DL → any D ≥ 1, with a tree of depth exactly DL; reason: the proof of Lemma 1 uses only D ≥ 1 and ν ≤ θ/(512D); the paper's D is one such value
--   - encoding: copies k = 1..κ, rounds t = 1..D, "for every realization of the noise", ∇ → 0-based Fin κ, Fin D; every noise assignment with values in [−ν, ν]; fderiv ℝ; reason: Lean conventions; same instances
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Lemma 1, p.21 (construction §7, pp.18–20; Eq. (12), p.21)

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data_IsValid
import Definitions.Def_GradSuffice_Thm8Data_f
import Definitions.Def_GradSuffice_Thm8Data_ftrunc
import Definitions.Def_GradSuffice_Thm8Data_Cond12
import Definitions.Def_GradSuffice_Thm8Data_fbar
import Definitions.Def_GradSuffice_Thm8Data_ftruncBar

namespace GradSuffice

/-- **Lemma 1 (truncation).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Lemma 1, p.21: "If `w` satisfies Eq. (12) for `t` and `k`, then for
every realization of the noise `f(w) = f_{t,k}(w)`, (13) and consequently `f̄(w) = f̄_{t,k}(w)` and
`∇f̄(w) = ∇f̄_{t,k}(w)`."

**Formalization Note.** The construction of §7 is `Thm8Data` with its validity conditions; the
branches and witnesses are fixed (Lemma 1 holds for every realization of them). A realization of
the noise is any `Z` with values in `[−ν, ν]`; the gradient is the Fréchet derivative. 0-based
`t`, `k`. -/
theorem lemma_1 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (W : Set X) (c : Thm8Data X) (hc : c.IsValid W)
    (t : Fin c.D) (k : Fin c.κ) (w : X) (h12 : c.Cond12 t k w) :
    (∀ Z : c.NoiseIdx → ℝ, (∀ i, Z i ∈ Set.Icc (-c.ν) c.ν) → c.f Z w = c.ftrunc t k Z w) ∧
      c.fbar w = c.ftruncBar t k w ∧ fderiv ℝ c.fbar w = fderiv ℝ (c.ftruncBar t k) w := by sorry

end GradSuffice
