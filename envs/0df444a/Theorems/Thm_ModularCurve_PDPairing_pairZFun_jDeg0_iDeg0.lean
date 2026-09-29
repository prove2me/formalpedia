-- Prove2me | Theorems.Thm_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0
-- name    : ModularCurve.PDPairing.pairZFun_jDeg0_iDeg0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/8e58b4fe-6380-5521-b5e1-45e7444258ce
-- title:
--   Degeneracy maps are adjoint for the integer parabolic pairing
-- statement:
--   Fix natural numbers $N$, $N'$, $d$, all nonzero, with $N \mid N'$ and $d \mid N'/N$, and work under the standing assumption that $\Gamma(4)$ is a free group. Let $x' : \mathrm{Additive}\,\Gamma_0(N') \to \mathbb{Z}$ and $y : \mathrm{Additive}\,\Gamma_0(N) \to \mathbb{Z}$ be additive homomorphisms out of the additivisations of the two congruence subgroups, each assumed parabolic in the sense of `IsParabolicHom`, i.e. vanishing on every element whose underlying integral matrix has trace squared equal to $4$. The assertion is the adjointness $\langle j_d x', y\rangle_N = \langle x', i_d y\rangle_{N'}$ for the integral pairing `pairZFun`, which on level $M$ sends $(\varphi,\psi)$ to the natural-number quotient $48 / [\Gamma_0(M) : \Gamma_0(M)\cap\Gamma(4)]$, cast to $\mathbb{Z}$, times the sum over the cusps of $\Gamma_0(M)\cap\Gamma(4)$ of `hPrim` (the first component of `sect`) of the restrictions of $\varphi$ and $\psi$ to that intersection, evaluated at the chosen cusp generators. Here $i_d$ is `iDeg0`, precomposition with the injection $\iota_d$ = `iotaDeg0` of $\Gamma_0(N')$ into $\Gamma_0(N)$ by conjugation with `conjLowerMat d`, while $j_d$ is `jDeg0`, the additive transfer (corestriction) to $\mathrm{Additive}\,\Gamma_0(N)$ of the homomorphism on the range of $\iota_d$ obtained from $x'$ by transport along the inverse of the isomorphism $\Gamma_0(N') \cong \mathrm{range}\,\iota_d$.
--
--   This is the projection formula for the degeneracy maps of prime-to-level degree $d$ between the levels $N$ and $N'$: push-forward by transfer and pull-back by conjugation-inclusion are adjoint for the integral pairing on parabolic homomorphisms. It is used in the construction of perfect self-adjoint pairings on cohomological carriers and in the level-raising arguments that compare eigenform supports at levels $N$ and $N'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0.lean

import Definitions.Def_ModularCurve_PDPairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup ModularCurve.Period in

theorem ModularCurve.PDPairing.pairZFun_jDeg0_iDeg0 (N N' d : ℕ) [NeZero N] [NeZero N'] [NeZero d]
    [IsFreeGroup ↥(Gamma 4)] (hNN' : N ∣ N') (hdd : d ∣ N' / N)
    (x' : Additive ↥(Gamma0 N') →+ ℤ) (y : Additive ↥(Gamma0 N) →+ ℤ)
    (hx' : IsParabolicHom (Gamma0 N') x') (hy : IsParabolicHom (Gamma0 N) y) :
    ModularCurve.PDPairing.pairZFun N (ModularCurve.PDPairing.jDeg0 N N' d ℤ ℤ hNN' hdd x') y =
      ModularCurve.PDPairing.pairZFun N' x' (ModularCurve.PDPairing.iDeg0 N N' d ℤ ℤ hNN' hdd y) := by sorry
