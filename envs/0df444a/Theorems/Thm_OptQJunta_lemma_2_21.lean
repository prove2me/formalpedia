-- Prove2me | Theorems.Thm_OptQJunta_lemma_2_21
-- name    : OptQJunta.lemma_2_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:21:15.798204+00:00
-- url     : https://prove2.me/theorems/acf84ca7-6698-45be-8a57-1d13280be1f9
-- title:
--   Lemma 2.21 — $\mathrm{Inf}_{\overline T}[f]\ge2\,\mathrm{dist}_{\mathcal B}(f,\mathcal B_T)$ and $\mathrm{dist}_{\mathcal B}(f,\mathcal B_T)\ge\mathrm{Inf}_i[f]/2$ for $i\in\overline T$
-- statement:
--   Fix $f:\{0,1\}^n\to\{0,1\}$ and $T\subseteq[n]$, and write $\overline T=[n]\setminus T$.
--
--   1. $\mathrm{Inf}_{\overline T}[f]\ge2\,\mathrm{dist}_{\mathcal B}(f,\mathcal B_T)$.
--   2. For every $i\in\overline T$, $\mathrm{dist}_{\mathcal B}(f,\mathcal B_T)\ge\mathrm{Inf}_i[f]/2$.
--
--   $$
--   2\,\mathrm{dist}_{\mathcal B}(f,\mathcal B_T)\le\mathrm{Inf}_{\overline T}[f],\qquad \mathrm{Inf}_i[f]\le2\,\mathrm{dist}_{\mathcal B}(f,\mathcal B_T)\quad(i\notin T).
--   $$
--
--   Influence outside $T$ thus controls the distance to $T$-juntas in both directions; part 1 turns distance into Fourier mass for the testers, and part 2 certifies farness in the lower bound.
--
--   Differences from the source:
--   - encoding: bits $\{0,1\}$, coordinates $[n]=\{1,\dots,n\}$ → bits `Bool` (`QAlgorithms.Qubits n = Fin n → Bool`), coordinates `Fin n` from $0$; reason: a relabelling; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Lemma 2.21, p.19

import Mathlib
import Definitions.Def_OptQJunta_infl
import Definitions.Def_OptQJunta_IsFar

open QAlgorithms

namespace OptQJunta

/-- **Lemma 2.21** (Influence controls Boolean junta distance; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.19). Fix
`f : {0,1}^n → {0,1}` and `T ⊆ [n]`.
(i) `Inf_{T̄}[f] ≥ 2 dist_ℬ(f, ℬ_T)`.
(ii) For every `i ∈ T̄`, `dist_ℬ(f, ℬ_T) ≥ Inf_i[f]/2`.

**Formalization Note** `T̄ = [n] ∖ T` is `Tᶜ` and `Inf_i[f] = infl f {i}`. -/
theorem lemma_2_21 {n : ℕ} (f : Qubits n → Bool) (T : Finset (Fin n)) :
    2 * distT f T ≤ infl f Tᶜ ∧ ∀ i : Fin n, i ∉ T → infl f {i} / 2 ≤ distT f T := by sorry

end OptQJunta
