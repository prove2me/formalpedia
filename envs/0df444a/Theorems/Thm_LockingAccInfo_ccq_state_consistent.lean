-- Prove2me | Theorems.Thm_LockingAccInfo_ccq_state_consistent
-- name    : LockingAccInfo.ccq_state_consistent
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:17.960049+00:00
-- url     : https://prove2.me/theorems/66e3d663-45bf-413a-954a-bc0c154cd92e
-- title:
--   §III — Eq. (3) is a consistent {ccq}-state, and $\rho_{YE}=\rho_Y\otimes\rho_E$ with $\rho_E$ fully mixed
-- statement:
--   Let $m\ge1$, let $(X,Y)$ be uniform on $\{0,1\}\times\{1,2,3\}^m$ and let $\rho_{E|(X,Y)=(x,y)}=2^{-m}(\mathrm{id}+(-1)^x\sigma_y)$ (Eq. (3)). Then:
--
--   1. the probabilities sum to $1$ and every $\rho_{E|(X,Y)=(x,y)}$ is a density matrix, so (3) describes a {ccq}-state $\rho_{XYE}$;
--   2. for every $y$ the state of $E$ given $Y=y$ is the fully mixed state:
--
--   $$
--   \sum_{x\in\{0,1\}}P_{X|Y=y}(x)\,\rho_{E|(X,Y)=(x,y)}=2^{-m}\,\mathrm{id},
--   $$
--
--   which is the statement $\rho_{YE}=\rho_Y\otimes\rho_E$;
--   3. the marginal state of $E$ is $\rho_E=\sum_{x,y}P_{XY}(x,y)\rho_{E|(X,Y)=(x,y)}=2^{-m}\mathrm{id}$.
--
--   Clause 3 is what makes $\mathcal N$ a POVM in the proof of Lemma 2, and clause 2 gives the decomposition (6).
--
--   Differences from the source:
--   - encoding: m ∈ ℕ in the state (3) → hypothesis 1 ≤ m; reason: a nondegeneracy condition that only excludes an undefined case: at m = 0 the operators (3) are the scalars 2 and 0, not states
--   - encoding: X = {0,1}, PXY uniform → Bool with false = 0, prob = 1/(2·3^m); reason: Lean convention; the same distribution
--   - encoding: ρ_YE = ρ_Y ⊗ ρ_E with ρ_E fully mixed → for every y, Σ_x P_{X|Y=y}(x) ρ_{E|(X,Y)=(x,y)} = 2^{−m} id, and ensembleMean = 2^{−m} id; reason: for a classical Y with P_Y(y) > 0 for all y, ρ_YE = ρ_Y ⊗ ρ_E is exactly the statement that every conditional state of E given Y = y equals ρ_E
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, §III, p.2 (consistency) and p.3 (ρ_YE = ρ_Y ⊗ ρ_E)

import Mathlib
import Definitions.Def_LockingAccInfo_lockEnsemble
open QAlgorithms (IsPOVM IsDensityMatrix effectProb)
open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData accessibleInformation ensembleMean)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, §III, p.2: "It is straightforward
to check that this is a consistent description of a {ccq}-state ρXYE", and p.3: "Using the fact
that ρYE = ρY ⊗ ρE where ρE is the fully mixed state".

Three clauses, for `m ≥ 1`: (a) uniform probabilities together with the operators (3) form a
valid classical-quantum ensemble (probabilities summing to 1, every ρE|(X,Y)=(x,y) a density
matrix); (b) for each y, the state of E given Y = y, Σ_x PX|Y=y(x) ρE|(X,Y)=(x,y), is the fully
mixed state 2^{−m} id, which is ρYE = ρY ⊗ ρE; (c) the marginal ρE is the fully mixed state.

**Formalization Note.** `1 ≤ m` is needed: at `m = 0` the operators (3) are the scalars 2 and
0, not states. Validity is the published `CQData.Valid`; ρE is the published `ensembleMean`. -/
theorem ccq_state_consistent (m : ℕ) (hm : 1 ≤ m) :
    (lockEnsemble m).Valid ∧
    (∀ y : Fin m → Fin 3,
      ∑ x : Bool, ((((lockEnsemble m).prob (x, y) / yMarginal m y : ℝ)) : ℂ) • lockState x y =
        ((2 : ℂ) ^ m)⁻¹ • 1) ∧
    ensembleMean (lockEnsemble m) = ((2 : ℂ) ^ m)⁻¹ • 1 := by sorry

end LockingAccInfo
