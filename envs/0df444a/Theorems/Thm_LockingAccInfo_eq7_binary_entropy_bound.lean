-- Prove2me | Theorems.Thm_LockingAccInfo_eq7_binary_entropy_bound
-- name    : LockingAccInfo.eq7_binary_entropy_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:07.3152+00:00
-- url     : https://prove2.me/theorems/eb440f51-84c1-486c-964a-f0b2c7d5cbc6
-- title:
--   Eq. (7) — $\mathbb E_{y}[H(\mathcal N_y[\sigma])]\ge1-\frac1{|\mathcal Y|}\sum_y|\operatorname{tr}(\sigma_y\sigma)|$
-- statement:
--   Let $m\ge1$, $\mathcal Y=\{1,2,3\}^m$, and let $\mathcal N_y$ be the binary POVMs of Eq. (6). For every state $\sigma$ on $(\mathbb C^2)^{\otimes m}$,
--
--   $$
--   \mathop{\mathbb E}_{y\leftarrow P_Y}\bigl[H(\mathcal N_y[\sigma])\bigr]\;\ge\;1-\frac1{|\mathcal Y|}\sum_{y\in\mathcal Y}\bigl|\operatorname{tr}(\sigma_y\sigma)\bigr| ,
--   $$
--
--   with entropies in bits. The outcome of $\mathcal N_y$ on $\sigma$ is a biased coin with bias $\operatorname{tr}(\sigma_y\sigma)$, so (7) says that on average over $y$ these coins are nearly fair unless $\sigma$ has large overlap with many $\sigma_y$.
--
--   Differences from the source:
--   - encoding: m ∈ ℕ in the state (3) → hypothesis 1 ≤ m; reason: a nondegeneracy condition that only excludes an undefined case: at m = 0 the operators (3) are the scalars 2 and 0, not states
--   - encoding: tr(σ_yσ) (real-valued for a state σ) → the real part of tr(σ_yσ); reason: tr(σ_yσ) is real for a state (Eq. (11)); same numbers
--   - encoding: log (base implied by 1 + H(Y) = H(XY)) → Shannon entropy in bits (Real.logb 2, 0 log 0 = 0); reason: the paper's own convention; h(p) ≥ 1 − |2p − 1| and H(XY) = 1 + H(Y) hold only in base 2
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, §III, Eq. (7), p.3

import Mathlib
import Definitions.Def_LockingAccInfo_lockEnsemble
import Definitions.Def_LockingAccInfo_outcomeEntropy
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
open QMaxCutSDP.Rounding (pauli pauliString)
open QAlgorithms (IsPOVM IsDensityMatrix effectProb)
open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData accessibleInformation ensembleMean)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, Eq. (7), p.3:
"E_{y←PY}[H(Ny[σ])] ≥ 1 − (1/|Y|) Σ_{y∈Y} |tr(σyσ)| . (7)" for every state σ on (C2)⊗m, where
Ny := {d · PX|Y=y(x) · ρE|(X,Y)=(x,y)}x∈X and Y = {1, 2, 3}^m.

**Formalization Note.** Ny is `lockBlockPOVM m y`, the expectation is the PY-weighted sum with
PY = `yMarginal m`, |Y| is the cardinality of `Fin m → Fin 3`, and σy for y ∈ {1, 2, 3}^m is
`pauliString` with letters shifted by `Fin.succ`. tr(σyσ) is real for a state σ (Eq. (11)); the
statement uses its real part. Entropies are in bits. `1 ≤ m` as (3) is not a state at
`m = 0`. -/
theorem eq7_binary_entropy_bound (m : ℕ) (hm : 1 ≤ m)
    (σ : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) (hσ : IsDensityMatrix σ) :
    1 - (1 / (Fintype.card (Fin m → Fin 3) : ℝ)) *
        ∑ y : Fin m → Fin 3, |(pauliString (fun i => (y i).succ) * σ).trace.re| ≤
      ∑ y, yMarginal m y * outcomeEntropy (lockBlockPOVM m y) σ := by sorry

end LockingAccInfo
