-- Prove2me | Theorems.Thm_LockingAccInfo_lemma2_accessible_information_bound
-- name    : LockingAccInfo.lemma2_accessible_information_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:21.265969+00:00
-- url     : https://prove2.me/theorems/01c7bcc0-4a32-4fb7-ad79-560eec8c2629
-- title:
--   Lemma 2 — $I_{\mathrm{acc}}(XY;E)\le(2/3)^{m/2}$
-- statement:
--   Let $m\ge1$ and let $\rho_{XYE}$ be the {ccq}-state of Eq. (3): $(X,Y)$ uniform on $\{0,1\}\times\{1,2,3\}^m$ and $E$ in the state $2^{-m}(\mathrm{id}+(-1)^x\sigma_y)$. Then the accessible information of $E$ on the pair $(X,Y)$ satisfies
--
--   $$
--   I_{\mathrm{acc}}(XY;E)\;\le\;\Bigl(\frac23\Bigr)^{m/2},
--   $$
--
--   where $I_{\mathrm{acc}}(V;E)=\max_MI(V;Z)$ is the largest mutual information (in bits) between $V$ and the outcome $Z$ of a POVM $M$ on $E$.
--
--   Without $Y$, every measurement on $E$ learns almost nothing about $(X,Y)$, although $H(XY)=1+m\log_23$ bits are encoded in $E$.
--
--   Differences from the source:
--   - encoding: m ∈ ℕ in the state (3) → hypothesis 1 ≤ m; reason: a nondegeneracy condition that only excludes an undefined case: at m = 0 the operators (3) are the scalars 2 and 0, not states
--   - encoding: Iacc = max over all local POVMs M of I(V;Z) → published accessibleInformation: sSup over finite POVMs with any number of outcomes of H(V) + H(Z) − H(VZ); reason: for a finite ensemble the optimum is attained by a finite POVM; the value set is nonempty and bounded above by H(V) (proved in the sanity file), so sSup is the maximum
--   - encoding: (2/3)^{m/2} → Real.rpow (2/3) ((m : ℝ)/2); reason: the real power with a real exponent
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, §III, Lemma 2, p.2

import Mathlib
import Definitions.Def_LockingAccInfo_lockEnsemble
open QAlgorithms (IsPOVM IsDensityMatrix effectProb)
open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData accessibleInformation ensembleMean)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, Lemma 2, p.2: "Let ρXYE be the
{ccq}-state defined above. Then Iacc(XY; E) ≤ (2/3)^{m/2}."

**Formalization Note.** Iacc is the published `accessibleInformation`: the supremum, over every
finite POVM on E (any number of outcomes), of the mutual information I(XY; Z) between the label and
the outcome, in bits. `(2/3)^{m/2}` is the real power with exponent `(m : ℝ)/2`. `1 ≤ m` as (3)
is not a state at `m = 0`. -/
theorem lemma2_accessible_information_bound (m : ℕ) (hm : 1 ≤ m) :
    accessibleInformation (lockEnsemble m) ≤ (2 / 3 : ℝ) ^ ((m : ℝ) / 2) := by sorry

end LockingAccInfo
