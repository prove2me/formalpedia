-- Prove2me | Theorems.Thm_MazurProof_N13GlobalKummerSimpleRootParity_localF_derivative_isUnit
-- name    : MazurProof.N13GlobalKummerSimpleRootParity.localF_derivative_isUnit
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T06:39:21.679738+00:00
-- url     : https://prove2.me/theorems/4b2d3bb1-92cf-4d1f-bbcc-c27a0286ccb8
-- title:
--   Mazur 13 port: localF_derivative_isUnit
-- statement:
--   Away from the different, the local sextic derivative is a unit.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GlobalKummerSimpleRootParity.lean#L202

import Mathlib
import Definitions.Def_MazurN13_L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GlobalKummerSimpleRootParity
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.fieldL
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.charZeroL
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.charZeroCompletion

theorem MazurProof.N13GlobalKummerSimpleRootParity.localF_derivative_isUnit (P : HeightOneSpectrum O) (hdifferent : integralEval N13SexticIrreducible.fInt.derivative ∉ P.asIdeal) : IsUnit ((localF P).derivative.eval (localTheta P)) := by sorry
