-- Prove2me | Theorems.Thm_OptQJunta_lemma_4_3
-- name    : OptQJunta.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:21:31.147113+00:00
-- url     : https://prove2.me/theorems/a8d17080-31ab-467e-89be-f0620a048182
-- title:
--   Lemma 4.3 — pair-fiber identities $\nu_J=2^{-|J|}\sum_u2\mu_u(1-\mu_u)$ and $q_J=2\nu_J$
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ and $J\subseteq[n]$, and let $q_J=\mathrm{Inf}_{\overline J}[f]$. Then
--
--   $$
--   \nu_J=2^{-|J|}\sum_{u\in\{0,1\}^{|J|}}2\mu_u(1-\mu_u),\qquad q_J=2\nu_J .
--   $$
--
--   Moreover, $\mu_u\le2^{|J|}\nu_J$ for every $u$, and $\nu_J\le\nu_{J'}$ whenever $J'\subseteq J$.
--
--   These identities relate the pair statistic sampled by partial support recovery to the Fourier mass outside $J$.
--
--   Differences from the source:
--   - encoding: $u\in\{0,1\}^{|J|}$ (coordinates of $J$ ordered by index) → $u$ : `J → Bool`; reason: a relabelling of the fibers
--   - encoding: bits $\{0,1\}$, coordinates $[n]=\{1,\dots,n\}$ → bits `Bool` (`QAlgorithms.Qubits n = Fin n → Bool`), coordinates `Fin n` from $0$; reason: a relabelling; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Lemma 4.3, p.55

import Mathlib
import Definitions.Def_OptQJunta_infl
import Definitions.Def_OptQJunta_nuJ

open QAlgorithms

namespace OptQJunta

/-- **Lemma 4.3** (Pair-fiber identities; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.55). For every `J ⊆ [n]`, we have
`ν_J = 2^{−|J|} Σ_u 2μ_u(1 − μ_u)` and `q_J = 2ν_J`. Moreover, `μ_u ≤ 2^{|J|} ν_J` for every `u`, and
`ν_J ≤ ν_{J′}` whenever `J′ ⊆ J`.

**Formalization Note** `f : {0,1}^n → {0,1}` is arbitrary (§4.1.1); `q_J = Inf_{J̄}[f]` is
`infl f Jᶜ`; `u` ranges over `{0,1}^{|J|}`, encoded as `J → Bool`. -/
theorem lemma_4_3 {n : ℕ} (f : Qubits n → Bool) (J : Finset (Fin n)) :
    nuJ f J = ((2 : ℝ) ^ J.card)⁻¹ *
        ∑ u : J → Bool, 2 * minorityDensity f J u * (1 - minorityDensity f J u) ∧
      infl f Jᶜ = 2 * nuJ f J ∧
      (∀ u : J → Bool, minorityDensity f J u ≤ (2 : ℝ) ^ J.card * nuJ f J) ∧
      ∀ J' : Finset (Fin n), J' ⊆ J → nuJ f J ≤ nuJ f J' := by sorry

end OptQJunta
