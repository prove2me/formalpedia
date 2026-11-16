-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_parity_conditioned_states
-- name    : FourWayStream.ARHM.Supplement.parity_conditioned_states
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:08:30.483208+00:00
-- url     : https://prove2.me/theorems/dab10679-ff3f-40f6-9c6f-d1385532cca0
-- title:
--   Lemma 7.8 — parity-conditioned states: $\rho_{J,0}-\rho_{J,1}=2\hat\rho(S_J)$, optimal prediction $\frac12+\frac12\|\hat\rho(S_J)\|_{\mathrm{tr}}$
-- statement:
--   Let $w,r\ge1$ and let $X\mapsto\rho_X$ assign a density matrix to every $X=(X^1,\dots,X^r)\in(\{0,1\}^w)^r$. For fixed $J\in[w]^r$ and $b\in\{0,1\}$ let $\rho_{J,b}=\mathbb E_X[\rho_X\mid Z_J(X)=b]$ for a uniform $X$, where $Z_J(X)=\bigoplus_iX^i_{J_i}$. Then
--   $$\rho_{J,0}-\rho_{J,1}=2\hat\rho(S_J),$$
--   with $\hat\rho(S)=\mathbb E_X[\chi_S(X)\rho_X]$ and $S_J=\{(1,J_1),\dots,(r,J_r)\}$, and the optimal probability, over all measurements of the message, of predicting $Z_J(X)$ is
--   $$\frac12+\frac12\,\|\hat\rho(S_J)\|_{\mathrm{tr}}.$$
--
--   So Bob's advantage on a fixed index tuple is exactly half the trace norm of one Fourier coefficient of the encoding, on a set of size $r$.
--
--   **Formalization Note** The optimal probability is the supremum over two-outcome POVMs; $\|A\|_{\mathrm{tr}}=\mathrm{Tr}\sqrt{A^\dagger A}$.
--
--   Differences from the source:
--   - encoding: the optimal probability of predicting Z_J(X) from the message → the supremum of the prediction probability over all two-outcome POVMs; reason: the set is nonempty and bounded by 1, and the optimum over measurements is this supremum (it is attained)
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.36, Lemma 7.8

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC
import Definitions.Def_FourWayStream_ARHM_Supplement_BlockXOR

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Lemma 7.8 (Parity-conditioned states), p.36. Let `w, r ≥ 1` and let `X ↦ ρ_X` be an encoding of
`X ∈ ({0,1}^w)^r` into density matrices. For fixed `J` and `b ∈ {0, 1}`, with
`ρ_{J,b} = E_X[ρ_X | Z_J(X) = b]` for a uniform `X`: `ρ_{J,0} − ρ_{J,1} = 2 ρ̂(S_J)`, and the optimal
probability of predicting `Z_J(X)` from the message is `1/2 + (1/2) ‖ρ̂(S_J)‖_tr`. -/
theorem parity_conditioned_states (w r d : ℕ) (hw : 1 ≤ w) (hr : 1 ≤ r)
    (ρ : (Fin r → Fin w → Bool) → Matrix (Fin d) (Fin d) ℂ) (hρ : ∀ X, IsDensityMatrix (ρ X))
    (J : Fin r → Fin w) :
    condState ρ J false - condState ρ J true = (2 : ℂ) • fourierCoeff ρ (blockSet J) ∧
    optPredict ρ J = 1 / 2 + 1 / 2 * trNorm (fourierCoeff ρ (blockSet J)) := by sorry

end FourWayStream.ARHM.Supplement
