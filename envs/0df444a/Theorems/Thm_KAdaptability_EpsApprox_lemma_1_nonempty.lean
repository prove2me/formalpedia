-- Prove2me | Theorems.Thm_KAdaptability_EpsApprox_lemma_1_nonempty
-- name    : KAdaptability.EpsApprox.lemma_1_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:00:43.880551+00:00
-- url     : https://prove2.me/theorems/b1dc28d4-7eb8-4a8c-b696-39b9d5c30b0c
-- title:
--   Proof of Lemma 1, p. ec6 — every ξ ∈ Ξ(ℓ) lies in Ξ_ε(ℓ) for all small ε, so Ξ_ε(ℓ) ≠ ∅
-- statement:
--   Fix a decision $(x,\{y^k\}_{k\in\mathcal K})\in\mathcal X\times\mathcal Y^K$ and an index vector $\ell\in\mathcal L=\{0,\dots,L\}^K$, and let $\Xi(\ell)$ and $\Xi_\varepsilon(\ell)$ be the exact and the approximate uncertainty sets of problems (6) and $(6_\varepsilon)$.
--
--   For every $\bar\xi\in\Xi(\ell)$ there is $\varepsilon'>0$ such that
--   $$\bar\xi\in\Xi_\varepsilon(\ell)\qquad\text{for all }\varepsilon\in(0,\varepsilon'].$$
--   In particular, if $\Xi(\ell)\ne\emptyset$, then $\Xi_\varepsilon(\ell)\ne\emptyset$ for all sufficiently small $\varepsilon>0$. (The paper takes $\varepsilon'=\min\{[Tx+Wy^k]_{\ell_k}-[H\bar\xi]_{\ell_k} : k\in\mathcal K,\ \ell_k\ne0\}$; when no $\ell_k$ is nonzero, $\Xi_\varepsilon(\ell)=\Xi(\ell)$ for every $\varepsilon$ and any $\varepsilon'>0$ works.)
--
--   This is the first step of the proof of Lemma 1 and the reason the effective domains of (6) and $(6_\varepsilon)$ agree for small $\varepsilon$.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec6 (PDF p. 40), proof of Lemma 1, first paragraph

import Mathlib
import Definitions.Def_KAdaptability_EpsApprox_Approx

namespace KAdaptability.EpsApprox

open Problem

/-- **Proof of Lemma 1, first step** (p. ec6). Fix a decision `(x, {y^k}_{k∈𝒦}) ∈ 𝒳 × 𝒴^K` and
`ℓ ∈ ℒ`. Every `ξ ∈ Ξ(ℓ)` lies in `Ξ_ε(ℓ)` for all `ε ∈ (0, ε′]`, for some `ε′ > 0`; in particular
`Ξ_ε(ℓ) ≠ ∅` for all sufficiently small `ε > 0` whenever `Ξ(ℓ) ≠ ∅`. -/
theorem lemma_1_nonempty {N M L nQ R K : ℕ} (P : Problem N M L nQ R)
    (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (hd : P.IsDecision x y)
    (ℓ : Fin K → Fin (L + 1)) :
    ∀ ξ ∈ P.XiL x y ℓ, ∃ ε' > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε', ξ ∈ P.XiEps ε x y ℓ := by sorry

end KAdaptability.EpsApprox
