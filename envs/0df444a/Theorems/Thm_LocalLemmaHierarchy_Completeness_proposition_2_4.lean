-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_proposition_2_4
-- name    : LocalLemmaHierarchy.Completeness.proposition_2_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T00:18:18.90653+00:00
-- url     : https://prove2.me/theorems/2f11a318-4b14-4433-9bca-d8fc51dc674b
-- title:
--   Proposition 2.4 — the negative diagonal is extremal: $R_U$ is the first positive zero of $P_U(t)$
-- statement:
--   Let $\mathcal R$ represent $Z$. For every finite region $U$,
--   $$R_U=\inf\{t>0:P_U(t)=0\}=\inf\{|z|:Z_U(z\mathbf 1)=0\},\qquad(2.9)$$
--   with empty infimum $+\infty$. This value is infinite exactly when $Z_U\equiv1$. If finite, $P_U(R_U)=0$, and the closed uniform polydisc of radius $t$ is zero-free exactly for $0\le t<R_U$.
--
--   Differences from the source:
--   - generalization: the sites form a countable set V → V is any type (no countability assumption); reason: no step of the proofs uses countability; the statement for countable V is the special case
--   - encoding: a total order ≺_{v,a} on D_{v,a} \ {v} → a rank R.rank v a : V → ℕ injective on D_{v,a} \ {v}, with w ≺ u ↔ rank w < rank u; reason: every total order on a finite set is induced by such a rank, and only comparisons are used
--   - encoding: a polynomial family Z = (Z_U)_{U ⋐ V} in the variables z_τ → Z : Finset V → MvPolynomial T ℝ, evaluated at complex z by MvPolynomial.aeval; reason: Z_∅ = 1 and the deletion identity with real c_{v,a} > 0 determine every Z_U recursively, so its coefficients are real; the source families are exactly these
--   - encoding: radii R_U, R, R_q in [0, +∞] (sup over t ≥ 0, inf over regions, empty infimum +∞) → ℝ≥0∞-valued ⨆ over t : ℝ≥0 and ⨅ over Finset V; reason: +∞ must be representable (constant families); ℝ≥0∞ suprema and infima are the extended-real ones
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Proposition 2.4, printed p. 7 (PDF p. 9); proof App. A.2, printed p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

/-- **Proposition 2.4 (The negative diagonal is extremal)**, printed p. 7 / PDF 9 (proof App. A.2,
printed 14 / PDF 16). For every finite region `U`,
`R_U = inf{t > 0 : P_U(t) = 0} = inf{|z| : Z_U(z·1) = 0}` (2.9), with empty infimum `+∞`; this
value is infinite exactly when `Z_U ≡ 1`; if finite, `P_U(R_U) = 0`; and the closed uniform polydisc
of radius `t` is zero-free exactly for `0 ≤ t < R_U`. -/
theorem proposition_2_4 {V T : Type} (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z) (U : Finset V) :
    regionRadius Z U =
        ⨅ (t : ℝ≥0) (_ : 0 < t ∧ negEval Z U (fun _ => (t : ℝ)) = 0), (t : ℝ≥0∞) ∧
    regionRadius Z U =
        ⨅ (z : ℂ) (_ : MvPolynomial.aeval (fun _ : T => z) (Z U) = 0), (‖z‖₊ : ℝ≥0∞) ∧
    (regionRadius Z U = ⊤ ↔ Z U = 1) ∧
    (regionRadius Z U ≠ ⊤ → negEval Z U (fun _ => (regionRadius Z U).toReal) = 0) ∧
    ∀ t : ℝ≥0, (ZeroFreeOn Z U (fun _ => (t : ℝ)) ↔ (t : ℝ≥0∞) < regionRadius Z U) := by sorry

end LocalLemmaHierarchy.Completeness
