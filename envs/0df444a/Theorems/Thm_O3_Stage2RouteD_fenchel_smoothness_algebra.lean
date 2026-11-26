-- Prove2me | Theorems.Thm_O3_Stage2RouteD_fenchel_smoothness_algebra
-- name    : O3.Stage2RouteD.fenchel_smoothness_algebra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:13:21.7435+00:00
-- url     : https://prove2.me/theorems/e1f3456a-b061-547d-8059-7ec83366216f
-- title:
--   Stage2 Route D: fenchel smoothness algebra
-- statement:
--   Pure algebra behind the conjugate-smoothness pivot.  Once the native
--   duality identities and the `q`-smoothness estimate supply these hypotheses,
--   the source-exact coefficient `σ/2` follows without loss.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteD.lean#L194-L225
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteD.lean#L194-L225

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD

theorem O3.Stage2RouteD.fenchel_smoothness_algebra {p q σ : ℝ} (hpq : p.HolderConjugate q)
    {d : ℕ} (x h a c : Point d)
    (_hσ : 0 ≤ σ)
    (hconst : (q - 1) * σ = 1)
    (hfenchelX :
      pairing a x - quadraticRegularizer q 0 a = quadraticRegularizer p 0 x)
    (hpairC : pairing c h = (lpNorm p h) ^ (2 : ℕ))
    (hnormStep : lpNorm q (σ • c) = σ * lpNorm p h)
    (hsmooth :
      quadraticRegularizer q 0 (a + σ • c) ≤
        quadraticRegularizer q 0 a + pairing x (σ • c) +
          ((q - 1) / 2) * (lpNorm q (σ • c)) ^ (2 : ℕ)) :
    quadraticRegularizer p 0 (x + h) ≥
      quadraticRegularizer p 0 x + pairing a h +
        (σ / 2) * (lpNorm p h) ^ (2 : ℕ) := by sorry
