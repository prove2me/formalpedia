-- Prove2me | Theorems.Thm_MultiSecretary_BR_online_le_offline
-- name    : MultiSecretary.BR.online_le_offline
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:57:03.165176+00:00
-- url     : https://prove2.me/theorems/a21f1424-2d78-4747-ba45-88e990656729
-- title:
--   Sec. 2, p. 5 — $V^\pi_{\mathrm{on}}(n,k)\le V^*_{\mathrm{off}}(n,k)$ for every feasible online policy
-- statement:
--   In the multi-secretary model with abilities $a_1>\dots>a_m>0$ and masses $f_j>0$, let $(n,k)\in\mathcal T$ and let $\pi\in\Pi(n,k)$ be a feasible online policy. Then
--   $$V^\pi_{\mathrm{on}}(n,k)\le V^*_{\mathrm{off}}(n,k).$$
--
--   The offline problem selects the best $k$ candidates on each realization, so it is a benchmark that no online policy can beat; regret is measured against it.
--
--   **Formalization Note** Policies are deterministic feasible online selection rules (see the model definition).
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Sec. 2, p. 5, display after 'Since the offline solution selects the best k candidates'

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model

namespace MultiSecretary.BR

open Finset

/-- Sec. 2, p. 5 (display after "Since the offline solution selects the best k candidates"):
no feasible online policy beats the offline benchmark, `V^π_on(n, k) ≤ V*_off(n, k)` for all
`(n, k) ∈ T` and all `π ∈ Π(n, k)`. -/
theorem online_le_offline {m : ℕ} (I : Instance m) (n k : ℕ) (hk : k ≤ n)
    (σ : (Fin n → Fin m) → Fin n → Bool) (hσ : σ ∈ policies n m k) :
    I.value σ ≤ I.Voff n k := by sorry

end MultiSecretary.BR
