-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_E_1
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_E_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:10:37.876677+00:00
-- url     : https://prove2.me/theorems/f81160f3-546e-405d-b57f-7752c1adaffa
-- title:
--   Theorem E.1 — a common alphabet for every monotone objective under directed constraints
-- statement:
--   Let $D=(V,A)$ be strongly connected with real arc costs and no negative directed cycle, with constraints $x_v-x_u\le c_{uv}$, finite report intervals $J_i$ of which at most $b$ may be violated, finite audit intervals, $b<n$ or at least one audit, $q=b+1$, and distinct source identities. For every vertex $v$ let $A^+_v$ contain the numerical values of the first $q$ sources in the increasing order of $\beta_a+d_D(a,v)$, and $A^-_v$ those of the first $q$ sources in the decreasing order of $\alpha_a-d_D(v,a)$, ties broken by fixed source identities. Each alphabet has at most $q$ values. For every coordinatewise nondecreasing $F:\mathbb R^V\to\mathbb R$, if the robust feasible class $C$ is nonempty then both extrema of $F$ are attained and
--   $$\max_{x\in C}F(x)=\max_{x\in C,\ x_v\in A^+_v}F(x),\qquad \min_{x\in C}F(x)=\min_{x\in C,\ x_v\in A^-_v}F(x).$$
--   The same alphabets preserve all monotone objectives simultaneously, without continuity or convexity of $F$.
--
--   Differences from the source:
--   - reading: ties broken by fixed source identities → every injective identity order; reason: the theorem holds for any fixed order
--   - encoding: max over C equals max over the alphabet-restricted class → some feasible field with values in A⁺_v attains the maximum of F over C (and A⁻_v for the minimum); reason: equivalent to the displayed identities with attainment
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem E.1, printed p.29 (PDF p.31)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_Directed

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem E.1, printed p.29 / PDF p.31. Strongly connected digraph with real arc costs and no
negative directed cycle, interval reports `[y̲_i, ȳ_i]` (at most `b` violated), finite audit
intervals, anchored (`b < n` or an audit), `q = b + 1`, distinct source identities ordered by
an injective `ord`. Each alphabet has at most `q` values, and for every coordinatewise
nondecreasing `F : ℝ^V → ℝ` (no continuity or convexity), if `C ≠ ∅` both extrema of `F` over `C`
are attained, at feasible fields with values in `A⁺_v` (maximum) and `A⁻_v` (minimum), so
`max_C F = max_{C, x_v ∈ A⁺_v} F` and `min_C F = min_{C, x_v ∈ A⁻_v} F`. -/
theorem theorem_E_1 (D : DirInst) (ord : Source D.n → ℕ) (hord : Function.Injective ord)
    (hn : 1 ≤ D.n) (hsc : StronglyConnected D) (hneg : NoNegCycle D)
    (hrep : ∀ i, D.repLo i ≤ D.repHi i) (haud : ∀ q ∈ D.audits, D.lo q ≤ D.hi q)
    (hA : D.budget < D.n ∨ D.audits.Nonempty) :
    (∀ v, (dirUp D ord v).card ≤ D.budget + 1 ∧ (dirLow D ord v).card ≤ D.budget + 1) ∧
    ∀ F : (Fin D.n → ℝ) → ℝ, Monotone F → (dirFeasible D).Nonempty →
      (∃ x ∈ dirFeasible D, (∀ v, x v ∈ dirUp D ord v) ∧ IsGreatest (F '' dirFeasible D) (F x)) ∧
      (∃ x ∈ dirFeasible D, (∀ v, x v ∈ dirLow D ord v) ∧ IsLeast (F '' dirFeasible D) (F x))
    := by sorry

end MeanCertificates1424.Hardness.Supplement
