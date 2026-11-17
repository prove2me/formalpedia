-- Prove2me | Theorems.Thm_KeystoneLadder_xPair_double_and_diffAddOrInf_EDS_core
-- name    : KeystoneLadder.xPair_double_and_diffAddOrInf_EDS_core
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:52.142946+00:00
-- url     : https://prove2.me/theorems/3768dd16-832e-4427-b3a7-8d4b08a89040
-- title:
--   Division-polynomial x-pairs satisfy the doubling and differential-addition recurrences
-- statement:
--   Let $W/k$ be an elliptic Weierstrass curve, let $m∈ℕ$ and $x∈k$, assume $4≠0$ in $k$, assume every nonzero-index division polynomial $ψ_n$ is nonzero, and assume $Ψ_3≠0$. Then the x-pair for $2m$ is nonzero and projectively equal to the doubled x-pair for $m$, while the x-pair for $2m+1$ is nonzero and projectively equal to differential addition from the pairs for $m$, $m+1$, and $1$: $$xPair_{2m}≠0∧Double(xPair_m)∼xPair_{2m}∧xPair_{2m+1}≠0∧DiffAdd(xPair_m,xPair_{m+1},xPair_1)∼xPair_{2m+1}.$$ This is the elliptic-divisibility-sequence core of the x-only ladder.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneLadder
import Definitions.Def_PsiInvariant
import Definitions.Def_KeystoneCoprimality
import Definitions.Def_WardSomos
import Definitions.Def_KeystoneDoubling

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical
variable {k : Type*} [Field k]
open KeystoneLadder
open KeystoneLadder.XOnly

theorem KeystoneLadder.xPair_double_and_diffAddOrInf_EDS_core
    (W : WeierstrassCurve k) [W.IsElliptic] (m : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    xPair W ((2 * m : ℕ) : ℤ) x ≠ 0 ∧
    SameP1Vec
      (XOnly.doubleVec (E := W⁄k) (xPair W (m : ℤ) x))
      (xPair W ((2 * m : ℕ) : ℤ) x) ∧
    xPair W ((2 * m + 1 : ℕ) : ℤ) x ≠ 0 ∧
    SameP1Vec
      (XOnly.diffAddOrInfVec (E := W⁄k)
        (xPair W (m : ℤ) x)
        (xPair W ((m + 1 : ℕ) : ℤ) x)
        (xPair W (1 : ℤ) x))
      (xPair W ((2 * m + 1 : ℕ) : ℤ) x) := by sorry
