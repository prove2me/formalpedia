-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_4_4
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:02:59.615195+00:00
-- url     : https://prove2.me/theorems/b37933a8-c0ef-4689-b8dc-48494000eb20
-- title:
--   Theorem 4.4 — simultaneous preservation of monotone objectives
-- statement:
--   In an anchored instance, every $x\in C_I(y)$ is bracketed by feasible fields $x^-,x^+$ with
--   $$x^-\le x\le x^+,\qquad x^-_v\in A^-_{v,b},\qquad x^+_v\in A^+_{v,b}\qquad(v\in V).$$
--   Consequently, for every coordinatewise nondecreasing $F:\mathbb R^V\to\mathbb R$, and simultaneously for all such $F$, the two alphabet families preserve the minimum and the maximum of $F$ over any nonempty $C_I(y)$: both extrema are attained, at feasible fields with values in $A^-_{v,b}$ (minimum) and $A^+_{v,b}$ (maximum), even if $F$ is discontinuous.
--
--   One finite representation serves every monotone target.
--
--   Differences from the source:
--   - reading: a fixed global order on identities → every injective identity order; reason: the theorem holds for any fixed order
--   - encoding: the alphabet families preserve the minimum and maximum of F → some feasible field with alphabet values attains the maximum (minimum) of F over C_I(y); reason: then the maximum over the alphabet-restricted class equals the maximum over C_I(y)
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 4.4, printed p.13 (PDF p.15)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_General

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem 4.4, printed p.13 / PDF p.15. In an anchored instance, every feasible field is
bracketed by feasible fields `x⁻ ≤ x ≤ x⁺` with `x⁻_v ∈ A⁻_{v,b}`, `x⁺_v ∈ A⁺_{v,b}`; hence for
every coordinatewise nondecreasing `F : ℝ^V → ℝ` (no continuity), over any nonempty `C_I(y)`
both extrema of `F` are attained, at fields with values in the two alphabet families, which
do not depend on `F`. -/
theorem theorem_4_4 (I : Inst) (hI : Valid I) (hA : Anchored I) (ord : Source I.n → ℕ)
    (hord : Function.Injective ord) :
    (∀ x ∈ CI I, ∃ xm ∈ CI I, ∃ xp ∈ CI I, (∀ v, xm v ≤ x v ∧ x v ≤ xp v) ∧
      ∀ v, xm v ∈ truncLow I ord v ∧ xp v ∈ truncUp I ord v) ∧
    (∀ F : (Fin I.n → ℝ) → ℝ, Monotone F → (CI I).Nonempty →
      (∃ x ∈ CI I, (∀ v, x v ∈ truncUp I ord v) ∧ IsGreatest (F '' CI I) (F x)) ∧
      (∃ x ∈ CI I, (∀ v, x v ∈ truncLow I ord v) ∧ IsLeast (F '' CI I) (F x))) := by sorry

end MeanCertificates1424.Hardness.Supplement
