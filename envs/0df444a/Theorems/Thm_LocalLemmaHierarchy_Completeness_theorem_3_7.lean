-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_3_7
-- name    : LocalLemmaHierarchy.Completeness.theorem_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:20:04.684386+00:00
-- url     : https://prove2.me/theorems/68758e10-c8e8-43ac-a0a2-681ac361b819
-- title:
--   Theorem 3.7 — completeness of finite memory: $R_q\uparrow R$, $\max\{0,R-1/(c_*q)\}\le R_q\le R$
-- statement:
--   For every positive local deletion representation $\mathcal R$ of $Z$, $R_q(\mathcal R)\uparrow R(Z)$ (nondecreasing in $q$ and convergent to $R(Z)$). If the family is nonconstant (equivalently, some option exists), then $R\le1/c_*$ and for $q\ge1$,
--   $$\max\Bigl\{0,R-\frac1{c_*q}\Bigr\}\le R_q(\mathcal R)\le R.\qquad(3.7)$$
--
--   Differences from the source:
--   - generalization: the sites form a countable set V → V is any type (no countability assumption); reason: no step of the proofs uses countability; the statement for countable V is the special case
--   - encoding: a total order ≺_{v,a} on D_{v,a} \ {v} → a rank R.rank v a : V → ℕ injective on D_{v,a} \ {v}, with w ≺ u ↔ rank w < rank u; reason: every total order on a finite set is induced by such a rank, and only comparisons are used
--   - encoding: a polynomial family Z = (Z_U)_{U ⋐ V} in the variables z_τ → Z : Finset V → MvPolynomial T ℝ, evaluated at complex z by MvPolynomial.aeval; reason: Z_∅ = 1 and the deletion identity with real c_{v,a} > 0 determine every Z_U recursively, so its coefficients are real; the source families are exactly these
--   - encoding: radii R_U, R, R_q in [0, +∞] (sup over t ≥ 0, inf over regions, empty infimum +∞) → ℝ≥0∞-valued ⨆ over t : ℝ≥0 and ⨅ over Finset V; reason: +∞ must be representable (constant families); ℝ≥0∞ suprema and infima are the extended-real ones
--   - encoding: R_q(R) ↑ R(Z) → Monotone (fun q => R_q) ∧ Tendsto (fun q => R_q) atTop (𝓝 R) in ℝ≥0∞; reason: the meaning of ↑
--   - encoding: max{0, R − 1/(c_∗ q)} → ENNReal.ofReal ((uniformRadius Z).toReal − 1/(c_∗ q)); reason: ofReal is max{0,·}; R is finite here by the conjunct R ≤ 1/c_∗, so toReal is exact
--   - encoding: "(equivalently, some option exists)" → the conjunct IsNonconstant Z ↔ ∃ v, Nonempty (R.Opt v); reason: the parenthetical is a claim of the theorem and is stated as such
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Theorem 3.7, printed p. 10 (PDF p. 12); proof App. B.5, printed p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory

open scoped ENNReal NNReal
open Filter Topology

namespace LocalLemmaHierarchy.Completeness

/-- **Theorem 3.7 (Completeness of finite memory)**, printed p. 10 / PDF 12 (proof App. B.5,
printed 19 / PDF 21). For every positive local deletion representation `R` of `Z`, `R_q(R) ↑ R(Z)`.
The family is nonconstant exactly when some option exists; then `R ≤ 1/c_∗` and, for `q ≥ 1`,
`max{0, R − 1/(c_∗ q)} ≤ R_q(R) ≤ R` (3.7). -/
theorem theorem_3_7 {V T : Type} (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z) :
    Monotone (fun q => memRadius R q) ∧
    Tendsto (fun q => memRadius R q) atTop (𝓝 (uniformRadius Z)) ∧
    (IsNonconstant Z ↔ ∃ v : V, Nonempty (R.Opt v)) ∧
    (IsNonconstant Z →
      uniformRadius Z ≤ ENNReal.ofReal (1 / R.cstar) ∧
      ∀ q : ℕ, 1 ≤ q →
        ENNReal.ofReal ((uniformRadius Z).toReal - 1 / (R.cstar * q)) ≤ memRadius R q ∧
        memRadius R q ≤ uniformRadius Z) := by sorry

end LocalLemmaHierarchy.Completeness
