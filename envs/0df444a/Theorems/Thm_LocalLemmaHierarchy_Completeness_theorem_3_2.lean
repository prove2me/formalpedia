-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_3_2
-- name    : LocalLemmaHierarchy.Completeness.theorem_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:19:50.033069+00:00
-- url     : https://prove2.me/theorems/c232d845-3e51-4db4-9621-f7a06417ec2d
-- title:
--   Theorem 3.2 — soundness and nesting: certificates give zero-freeness, $R_q\le R_{q+1}\le R$
-- statement:
--   Let $\mathcal R$ represent $Z$. A memory-$q$ certificate for nonnegative moduli $p$ makes every finite $Z_U$ nonzero throughout $|z_\tau|\le p_\tau$. For every $q\ge0$,
--   $$R_q(\mathcal R)\le R_{q+1}(\mathcal R)\le R(Z).\qquad(3.3)$$
--
--   Differences from the source:
--   - generalization: the sites form a countable set V → V is any type (no countability assumption); reason: no step of the proofs uses countability; the statement for countable V is the special case
--   - encoding: a total order ≺_{v,a} on D_{v,a} \ {v} → a rank R.rank v a : V → ℕ injective on D_{v,a} \ {v}, with w ≺ u ↔ rank w < rank u; reason: every total order on a finite set is induced by such a rank, and only comparisons are used
--   - encoding: a polynomial family Z = (Z_U)_{U ⋐ V} in the variables z_τ → Z : Finset V → MvPolynomial T ℝ, evaluated at complex z by MvPolynomial.aeval; reason: Z_∅ = 1 and the deletion identity with real c_{v,a} > 0 determine every Z_U recursively, so its coefficients are real; the source families are exactly these
--   - encoding: radii R_U, R, R_q in [0, +∞] (sup over t ≥ 0, inf over regions, empty infimum +∞) → ℝ≥0∞-valued ⨆ over t : ℝ≥0 and ⨅ over Finset V; reason: +∞ must be representable (constant families); ℝ≥0∞ suprema and infima are the extended-real ones
--   - encoding: x ∈ [0,1)^{S_q}, a vector on the states → x : Hist R → ℝ, constrained (0 ≤ x_s < 1 and the row inequality) only at states (IsMemState); reason: every row at a state reads only states (s ★_q (a,u) is again a state), so values elsewhere are irrelevant
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Theorem 3.2, printed p. 8 (PDF p. 10); proof App. B.1, printed p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

/-- **Theorem 3.2 (Soundness and nesting)**, printed p. 8 / PDF 10 (proof App. B.1, printed 17 /
PDF 19). A memory certificate for moduli `p` makes every finite `Z_U` nonzero throughout
`|z_τ| ≤ p_τ`; and for every `q ≥ 0`, `R_q(R) ≤ R_{q+1}(R) ≤ R(Z)` (3.3). -/
theorem theorem_3_2 {V T : Type} (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z) :
    (∀ (q : ℕ) (p : T → ℝ), (∀ τ, 0 ≤ p τ) → ∀ x : Hist R → ℝ, IsMemCertificate R q p x →
      ∀ U : Finset V, ZeroFreeOn Z U p) ∧
    ∀ q : ℕ, memRadius R q ≤ memRadius R (q + 1) ∧ memRadius R (q + 1) ≤ uniformRadius Z := by sorry

end LocalLemmaHierarchy.Completeness
