-- Prove2me | Theorems.Thm_MazurProof_N13GlobalKummerSimpleRootParity_normalizedKummerInteger_multiplicity_even_of_simpleRoot
-- name    : MazurProof.N13GlobalKummerSimpleRootParity.normalizedKummerInteger_multiplicity_even_of_simpleRoot
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-09T07:56:22.715004+00:00
-- url     : https://prove2.me/theorems/6a8dfeb7-f74a-4fb9-934c-a247cb0a5e5c
-- title:
--   Mazur 13 port: normalizedKummerInteger_multiplicity_even_of_simpleRoot
-- statement:
--   At every prime away from the different, the simple-root branch gives even multiplicity of the normalized Kummer integer, with no condition on the denominator-clearing scale.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GlobalKummerSimpleRootParity.lean#L383

import Mathlib
import Definitions.Def_MazurN13_L4

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

theorem MazurProof.N13GlobalKummerSimpleRootParity.normalizedKummerInteger_multiplicity_even_of_simpleRoot (D : N13LowDegreeKummerHom.LowRep) (P : HeightOneSpectrum O) (hmem : normalizedKummerInteger D ∈ P.asIdeal) (hdifferent : integralEval N13SexticIrreducible.fInt.derivative ∉ P.asIdeal) (hsimple : IsUnit ((localU D P).derivative.eval (localTheta P))) : Even (multiplicity P.asIdeal (Ideal.span {normalizedKummerInteger D})) := by sorry
