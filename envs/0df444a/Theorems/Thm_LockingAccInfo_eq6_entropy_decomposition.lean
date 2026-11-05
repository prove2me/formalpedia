-- Prove2me | Theorems.Thm_LockingAccInfo_eq6_entropy_decomposition
-- name    : LockingAccInfo.eq6_entropy_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:18.191612+00:00
-- url     : https://prove2.me/theorems/540494a2-6815-4d45-86dc-22a24a309acf
-- title:
--   Eq. (6) — $H(\mathcal N[\sigma])=H(Y)+\mathbb E_{y\leftarrow P_Y}[H(\mathcal N_y[\sigma])]$
-- statement:
--   Let $m\ge1$, $d=2^m$, and let $\rho_{XYE}$ be the {ccq}-state of Eq. (3), with $\mathcal N=\{d\cdot P_{XY}(x,y)\cdot\rho_{E|(X,Y)=(x,y)}\}_{(x,y)}$ and, for each $y\in\{1,2,3\}^m$, $\mathcal N_y=\{d\cdot P_{X|Y=y}(x)\cdot\rho_{E|(X,Y)=(x,y)}\}_{x\in\{0,1\}}$. For every state $\sigma$ on $E$,
--
--   $$
--   H(\mathcal N[\sigma])=H(Y)+\mathop{\mathbb E}_{y\leftarrow P_Y}\bigl[H(\mathcal N_y[\sigma])\bigr],
--   $$
--
--   with entropies in bits. The identity splits the outcome of $\mathcal N$ into the value of $Y$, which is uniform whatever $\sigma$ is because $\rho_{YE}=\rho_Y\otimes\rho_E$, and a binary outcome given $Y$.
--
--   Differences from the source:
--   - encoding: m ∈ ℕ in the state (3) → hypothesis 1 ≤ m; reason: a nondegeneracy condition that only excludes an undefined case: at m = 0 the operators (3) are the scalars 2 and 0, not states
--   - encoding: log (base implied by 1 + H(Y) = H(XY)) → Shannon entropy in bits (Real.logb 2, 0 log 0 = 0); reason: the paper's own convention; h(p) ≥ 1 − |2p − 1| and H(XY) = 1 + H(Y) hold only in base 2
--   - encoding: E_{y←P_Y}[H(𝒩_y[σ])], P_{X|Y=y}(x) → Σ_y P_Y(y)·H(𝒩_y[σ]) with P_Y the marginal of P_XY, P_{X|Y=y}(x) = P_XY(x,y)/P_Y(y); reason: the definitions of expectation and conditional probability
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, §III, Eq. (6), p.3

import Mathlib
import Definitions.Def_LockingAccInfo_lockEnsemble
import Definitions.Def_LockingAccInfo_outcomeEntropy
import Definitions.Def_LockingAccInfo_lemma5POVM
open QAlgorithms (IsPOVM IsDensityMatrix effectProb)
open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData accessibleInformation ensembleMean)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, Eq. (6), p.3: "H(N[σ]) = H(Y) +
E_{y←PY}[H(Ny[σ])] (6) where, for any y ∈ Y, H(Ny[σ]) is the entropy of the output of the POVM
Ny := {d · PX|Y=y(x) · ρE|(X,Y)=(x,y)}x∈X applied to σ", for every state σ on E, where
N = {d · PXY(x, y) · ρE|(X,Y)=(x,y)}(x,y) and d = 2^m (p.2).

**Formalization Note.** N is `lemma5POVM (lockEnsemble m)` (with dim E = 2^m), Ny is
`lockBlockPOVM m y`, H(Y) is the Shannon entropy of the marginal `yMarginal m` of Y, and the
expectation over y ← PY is the PY-weighted sum. Entropies are in bits. `1 ≤ m` as (3) is not a
state at `m = 0`. -/
theorem eq6_entropy_decomposition (m : ℕ) (hm : 1 ≤ m)
    (σ : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) (hσ : IsDensityMatrix σ) :
    outcomeEntropy (lemma5POVM (lockEnsemble m)) σ =
      shannon (yMarginal m) + ∑ y, yMarginal m y * outcomeEntropy (lockBlockPOVM m y) σ := by sorry

end LockingAccInfo
