-- Prove2me | Theorems.Thm_LockingAccInfo_lemma1_last_bit_measurement
-- name    : LockingAccInfo.lemma1_last_bit_measurement
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:50.502654+00:00
-- url     : https://prove2.me/theorems/35fd8795-dd4f-4510-a3ed-d75d7f7ab7f5
-- title:
--   Lemma 1 — given $Y=y$, a measurement of $E$ outputs $X$
-- statement:
--   Let $m\ge1$ and let $\rho_{XYE}$ be the {ccq}-state of Eq. (3). For every fixed value $y\in\{1,2,3\}^m$ of $Y$ there is a two-outcome POVM $\{M_0,M_1\}$ on $E$ (depending on $y$) such that for all $x,x'\in\{0,1\}$
--
--   $$
--   \operatorname{tr}\bigl(M_{x'}\,\rho_{E|(X,Y)=(x,y)}\bigr)=\begin{cases}1,&x'=x,\\0,&x'\ne x,\end{cases}
--   $$
--
--   that is, the measurement's output equals $X$ with certainty. This is the reason the accessible information jumps once $Y$ is known: it gives $I_{\mathrm{acc}}(XY;YE)=H(XY)$ and part (ii) of the paper's conclusion.
--
--   Differences from the source:
--   - encoding: m ∈ ℕ in the state (3) → hypothesis 1 ≤ m; reason: a nondegeneracy condition that only excludes an undefined case: at m = 0 the operators (3) are the scalars 2 and 0, not states
--   - encoding: a measurement of E with output equal to X → a POVM {M_x}_{x∈Bool} on E with tr(M_{x′} ρ_{E|(X,Y)=(x,y)}) = 1 if x′ = x and 0 otherwise; reason: the outcome equals X with certainty on each conditional state
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, Lemma 1, p.2

import Mathlib
import Definitions.Def_LockingAccInfo_lockState
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
open QAlgorithms (IsPOVM effectProb)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, Lemma 1, p.2: "Let ρXYE be the
{ccq}-state defined above. For any fixed value y ∈ Y of the random variable Y, there exists a
measurement of the quantum system E with output equal to X."

**Formalization Note.** For each `y` (the measurement may depend on `y`) there is a two-outcome
POVM `M` on E alone, indexed by the values `Bool` of X, such that on the state
ρE|(X,Y)=(x,y) of (3) outcome `x` occurs with probability 1 and the other outcome with
probability 0: "output equal to X". `1 ≤ m` as (3) is not a state at `m = 0`. -/
theorem lemma1_last_bit_measurement (m : ℕ) (hm : 1 ≤ m) (y : Fin m → Fin 3) :
    ∃ M : Bool → Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ, IsPOVM M ∧
      ∀ x x' : Bool, effectProb (M x') (lockState x y) = if x' = x then 1 else 0 := by sorry

end LockingAccInfo
