-- Prove2me | Theorems.Thm_LockingAccInfo_iacc_with_Y_eq_entropy
-- name    : LockingAccInfo.iacc_with_Y_eq_entropy
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:14.916577+00:00
-- url     : https://prove2.me/theorems/2b63c10c-9c1a-47e0-a59d-810ac7041c2d
-- title:
--   §III closing — $I_{\mathrm{acc}}(XY;EY)=H(XY)=1+m\log_23$
-- statement:
--   Let $m\ge1$ and let $\rho_{XYE}$ be the {ccq}-state of Eq. (3). If the classical value $Y$ is appended to $E$, a measurement of the combined system recovers $(X,Y)$ completely:
--
--   $$
--   I_{\mathrm{acc}}(XY;EY)=H(XY)=1+m\log_2 3 .
--   $$
--
--   Here $I_{\mathrm{acc}}(XY;EY)$ is the accessible information of the {cq}-state obtained by combining the systems $Y$ and $E$ (footnote 23), and $H(XY)$ is the Shannon entropy in bits of the uniform distribution on $\{0,1\}\times\{1,2,3\}^m$. With Lemma 2, the gain $\Delta=I_{\mathrm{acc}}(XY;EY)-I_{\mathrm{acc}}(XY;E)$ exceeds $H(Y)=m\log_23$: the locking effect.
--
--   Differences from the source:
--   - encoding: m ∈ ℕ in the state (3) → hypothesis 1 ≤ m; reason: a nondegeneracy condition that only excludes an undefined case: at m = 0 the operators (3) are the scalars 2 and 0, not states
--   - encoding: Iacc = max over all local POVMs M of I(V;Z) → published accessibleInformation: sSup over finite POVMs with any number of outcomes of H(V) + H(Z) − H(VZ); reason: for a finite ensemble the optimum is attained by a finite POVM; the value set is nonempty and bounded above by H(V) (proved in the sanity file), so sSup is the maximum
--   - encoding: Iacc(V; YE): systems Y and E combined (footnote 23) → withRegister: conditional state |π(v)⟩⟨π(v)| ⊗ ρ_{E|V=v} on the index type P × Q, register first; reason: the {cq}-state ρ_{V(YE)} of footnote 23; the order of the two factors does not change the accessible information
--   - encoding: log (base implied by 1 + H(Y) = H(XY)) → Shannon entropy in bits (Real.logb 2, 0 log 0 = 0); reason: the paper's own convention; h(p) ≥ 1 − |2p − 1| and H(XY) = 1 + H(Y) hold only in base 2
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, §III closing paragraph, p.3

import Mathlib
import Definitions.Def_LockingAccInfo_lockEnsemble
import Definitions.Def_LockingAccInfo_withRegister
open QAlgorithms (IsPOVM IsDensityMatrix effectProb)
open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData accessibleInformation ensembleMean)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, §III closing, p.3: "Because of
Lemma 1, we have Iacc(XY; EY) = H(XY)", for the {ccq}-state ρXYE of Eq. (3); together with the
value H(XY) = 1 + H(Y) = 1 + m log₂ 3 of the uniform distribution on {0, 1} × {1, 2, 3}^m (p.3:
"1 + H(Y) = H(XY)").

**Formalization Note.** Iacc(XY; EY) is the published `accessibleInformation` of the ensemble
whose quantum system is the combination of the classical register Y (basis state |y⟩) and E
(footnote 23, p.5), built with `withRegister` and the projection `(x, y) ↦ y`; POVMs act on the
composite system. Entropies are in bits. `1 ≤ m` as (3) is not a state at `m = 0`. -/
theorem iacc_with_Y_eq_entropy (m : ℕ) (hm : 1 ≤ m) :
    accessibleInformation (withRegister (fun v : Bool × (Fin m → Fin 3) => v.2) (lockEnsemble m)) =
      shannon (lockEnsemble m).prob ∧
    shannon (lockEnsemble m).prob = 1 + m * Real.logb 2 3 := by sorry

end LockingAccInfo
