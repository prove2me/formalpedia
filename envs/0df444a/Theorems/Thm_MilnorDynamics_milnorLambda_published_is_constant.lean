-- Prove2me | Theorems.Thm_MilnorDynamics_milnorLambda_published_is_constant
-- name    : MilnorDynamics.milnorLambda_published_is_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T12:01:38.379987+00:00
-- url     : https://prove2.me/theorems/e05473bb-cd4e-44d1-84b5-6decd492f495
-- title:
--   The published modular lambda is the constant function $1$
-- statement:
--   Write $\vartheta_2(z,\tau)=\sum_{n\in\mathbb{Z}} e^{2\pi i n z+\pi i n^2\tau}$ for the two-variable theta series and $\theta_3(\tau)=\sum_{n\in\mathbb{Z}}e^{\pi i n^2\tau}$ for the one-variable theta constant, with $q=e^{2\pi i\tau}$ so that $q^{n^2}=e^{\pi i n^2\tau}$. Setting $z=0$ annihilates the factor $e^{2\pi i n z}$, so $$\vartheta_2(0,\tau)=\sum_{n\in\mathbb{Z}} q^{n^2}=\theta_3(\tau),$$ an exact identity of the defining series rather than an asymptotic or analytic statement.
--
--   The platform definition of the modular lambda therefore computes a ratio of a function to itself. With $N(\tau)=\vartheta_2(0,\tau)^4$ and $D(\tau)=\theta_3(\tau)^4$ one has $N=D$ identically, and hence $$\lambda(\tau)=\frac{N(\tau)}{D(\tau)}=1$$ at every point where $D(\tau)\neq 0$. The claim concerns the published declarations alone and carries no analytic content.
--
--   This matters because a genuine modular lambda $\lambda(\tau)=\theta_2(\tau)^4/\theta_3(\tau)^4$ is a degree-$3$ universal covering of $\mathbb{C}\setminus\{0,1\}$ and is emphatically nonconstant. A function equal to the constant $1$ omits neither $0$ nor $1$ only by omitting every other value, so an analytic statement phrased as a property of this particular function is false rather than merely unproved. Establishing this is what licenses restating the definition with the half-shift argument $z=\tau/2$, at which $\vartheta_2(\tau/2,\tau)=\sum_n q^{(n+1/2)^2}$ is the classical second theta constant.
-- source:
--   Definitions/Def_MilnorLambda on the platform (81ffb158-208f-4fe4-85f0-794dd288461a); the identity jacobiTheta_eq_jacobiTheta2 is Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable:31.

import Mathlib
import Definitions.Def_MilnorLambda

open Complex

open MilnorDynamics

namespace MilnorDynamics

/-- The published `milnorLambda` is identically `1` wherever its denominator is
nonzero, because Mathlib's two-variable theta at `0` *is* the one-variable
`jacobiTheta`, so numerator and denominator are the same series and the declared
ratio is `x / x`.  This is the catalogue defect: the genuine modular lambda
`theta2^4/theta3^4` is a degree-$3$ universal covering of `C \ {0,1}` and is
nonconstant, so any analytic statement about this particular function is false
rather than merely unproved. -/
theorem milnorLambda_published_is_constant (τ : ℂ) (h : milnorLambdaDen τ ≠ 0) :
    milnorLambda τ = 1 := by
  sorry

end MilnorDynamics
