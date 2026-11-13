-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_lemma_3_6
-- name    : LocalLemmaHierarchy.Completeness.lemma_3_6
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T00:20:09.988656+00:00
-- url     : https://prove2.me/theorems/b42cee83-1076-4c7c-9b6f-f4b7e845f6ae
-- title:
--   Lemma 3.6 — suffix comparison: $F_{q,\nu}(Y^{(j)})\le Y^{(j-1)}$ for $Y^{(j)}_s=X^\nu_{\sigma_j(s)}$
-- statement:
--   Let $\mathcal R$ represent $Z$ and $0<\nu<R$. For a state $s$ let $\sigma_j(s)$ retain its last $j$ moves (or the whole shorter history) and $Y^{(j)}_s=X^\nu_{\sigma_j(s)}$, with $X^\nu$ the canonical exact branch of Proposition 3.4. Then $F_{q,\nu}(Y^{(j)})\le Y^{(j-1)}$ for $1\le j\le q$, at every state of $S_q$ (startup states included).
--
--   Differences from the source:
--   - generalization: the sites form a countable set V → V is any type (no countability assumption); reason: no step of the proofs uses countability; the statement for countable V is the special case
--   - encoding: a total order ≺_{v,a} on D_{v,a} \ {v} → a rank R.rank v a : V → ℕ injective on D_{v,a} \ {v}, with w ≺ u ↔ rank w < rank u; reason: every total order on a finite set is induced by such a rank, and only comparisons are used
--   - encoding: a polynomial family Z = (Z_U)_{U ⋐ V} in the variables z_τ → Z : Finset V → MvPolynomial T ℝ, evaluated at complex z by MvPolynomial.aeval; reason: Z_∅ = 1 and the deletion identity with real c_{v,a} > 0 determine every Z_U recursively, so its coefficients are real; the source families are exactly these
--   - encoding: radii R_U, R, R_q in [0, +∞] (sup over t ≥ 0, inf over regions, empty infimum +∞) → ℝ≥0∞-valued ⨆ over t : ℝ≥0 and ⨅ over Finset V; reason: +∞ must be representable (constant families); ℝ≥0∞ suprema and infima are the extended-real ones
--   - encoding: x ∈ [0,1)^{S_q}, a vector on the states → x : Hist R → ℝ, constrained (0 ≤ x_s < 1 and the row inequality) only at states (IsMemState); reason: every row at a state reads only states (s ★_q (a,u) is again a state), so values elsewhere are irrelevant
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Lemma 3.6, printed p. 9 (PDF p. 11); proof App. B.4, printed p. 18 (PDF p. 20)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

/-- **Lemma 3.6 (Suffix comparison)**, printed p. 9 / PDF 11 (proof App. B.4, printed 18 / PDF 20).
For `0 < ν < R`, the vectors `Y^(j)_s = X^ν_{σ_j(s)}` satisfy `F_{q,ν}(Y^(j)) ≤ Y^(j−1)` for
`1 ≤ j ≤ q`, at every state of `S_q`, startup states included. -/
theorem lemma_3_6 {V T : Type} (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (ν : ℝ) (hν : 0 < ν) (hνR : ENNReal.ofReal ν < uniformRadius Z) (q j : ℕ)
    (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    ∀ s : Hist R, IsMemState R q s →
      memUpdate R q (fun _ => ν) (fun s' => canonicalBranch R ν (s'.suffix j)) s ≤
        canonicalBranch R ν (s.suffix (j - 1)) := by sorry

end LocalLemmaHierarchy.Completeness
