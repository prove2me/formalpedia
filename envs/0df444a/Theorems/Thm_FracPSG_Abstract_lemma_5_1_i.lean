-- Prove2me | Theorems.Thm_FracPSG_Abstract_lemma_5_1_i
-- name    : FracPSG.Abstract.lemma_5_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:36.575352+00:00
-- url     : https://prove2.me/theorems/823f7138-afdc-4a6c-b50d-bb4d787be909
-- title:
--   Lemma 5.1(i) — Ω₀ is nonempty and h(zₙ) decreases to h(z̄)
-- statement:
--   Work in the setting of §5: $h:\mathcal K\to(-\infty,+\infty]$ proper and lower semicontinuous, $(z_n)$ a sequence in $\mathcal K$, $\alpha_n>0$, $\Delta_n\ge0$, and suppose that the sufficient decrease condition (H1) $h(z_{n+1})+\alpha_n\Delta_n^2\le h(z_n)$ and the continuity condition (H3) hold. Let $\Omega$ be the set of cluster points of $(z_n)$ and $\Omega_0=\{\bar z\in\Omega: h(z_n)\to h(\bar z)\}$. Then
--   $$\Omega_0=\{\bar z\in\mathcal K:\ \exists\, z_{k_n}\to\bar z \text{ with } h(z_{k_n})\to h(\bar z)\}\neq\emptyset,$$
--   and for every $\bar z\in\Omega_0$ the sequence $h(z_n)$ is nonincreasing and converges to $h(\bar z)$.
--
--   This identifies the set of "good" cluster points and shows that it is not empty, which every later statement of §5 uses.
--
--   **Formalization Note** "$h(z_n)\downarrow h(\bar z)$" is `Antitone` together with convergence in `EReal`. The paper's proof says "nondecreasing", a typo: (H1) makes the values nonincreasing. The statement does not assume $h(z_0)<+\infty$, which this part does not need.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 14, Lemma 5.1(i)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracPSG_Abstract_Basic

open Filter Topology

namespace FracPSG.Abstract

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

/-- Lemma 5.1(i) (Boţ–Dao–Li, arXiv:2003.04124v2, p. 14): under (H1) and (H3),
`Ω₀ = {z̄ : some subsequence z_{kₙ} → z̄ with h(z_{kₙ}) → h(z̄)}`, `Ω₀ ≠ ∅`, and `h(zₙ) ↓ h(z̄)` for
every `z̄ ∈ Ω₀` (the sequence `h(zₙ)` is nonincreasing and tends to `h(z̄)`). -/
theorem lemma_5_1_i {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ}
    {lam : ℤ → ℝ}
    (hset : AbstractSetting h α β ε Δ ilo ihi lam)
    (hH1 : H1 h z α Δ) (hH3 : H3 h z) :
    omega0 h z = {zbar | ∃ k : ℕ → ℕ, StrictMono k ∧
        Tendsto (fun n => z (k n)) atTop (𝓝 zbar) ∧
        Tendsto (fun n => h (z (k n))) atTop (𝓝 (h zbar))} ∧
      (omega0 h z).Nonempty ∧
      ∀ zbar ∈ omega0 h z, Antitone (fun n => h (z n)) ∧
        Tendsto (fun n => h (z n)) atTop (𝓝 (h zbar)) := by sorry

end FracPSG.Abstract
