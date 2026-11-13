-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_proposition_3_4
-- name    : LocalLemmaHierarchy.Completeness.proposition_3_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T00:19:16.958339+00:00
-- url     : https://prove2.me/theorems/dba20657-6417-4b4f-ad2e-476966f31784
-- title:
--   Proposition 3.4 — the canonical exact branch $X^\nu$: least fixed point, $0\le X^\nu\le \nu/R<1$
-- statement:
--   Let $\mathcal R$ represent $Z$ and $0<\nu<R$. There is a least exact branch $X^\nu$ satisfying
--   $$X^\nu_h=\Phi_{\nu,h}(X^\nu),\qquad 0\le X^\nu_h\le\nu/R<1\qquad(3.4)$$
--   for every ambient exact history $h$, with $\nu/\infty=0$; here it is the limit (supremum) of the finite-depth evaluations $X^{\nu,N}$ (B.2). It is invariant under symmetries preserving the representation. If an option is available at $h$, then $X^\nu_h\ge c_*\nu$; otherwise $X^\nu_h=0$.
--
--   Differences from the source:
--   - generalization: the sites form a countable set V → V is any type (no countability assumption); reason: no step of the proofs uses countability; the statement for countable V is the special case
--   - encoding: a total order ≺_{v,a} on D_{v,a} \ {v} → a rank R.rank v a : V → ℕ injective on D_{v,a} \ {v}, with w ≺ u ↔ rank w < rank u; reason: every total order on a finite set is induced by such a rank, and only comparisons are used
--   - encoding: a polynomial family Z = (Z_U)_{U ⋐ V} in the variables z_τ → Z : Finset V → MvPolynomial T ℝ, evaluated at complex z by MvPolynomial.aeval; reason: Z_∅ = 1 and the deletion identity with real c_{v,a} > 0 determine every Z_U recursively, so its coefficients are real; the source families are exactly these
--   - encoding: radii R_U, R, R_q in [0, +∞] (sup over t ≥ 0, inf over regions, empty infimum +∞) → ℝ≥0∞-valued ⨆ over t : ℝ≥0 and ⨅ over Finset V; reason: +∞ must be representable (constant families); ℝ≥0∞ suprema and infima are the extended-real ones
--   - generalization: there is a least exact branch X^ν satisfying (3.4) → the explicit branch canonicalBranch R ν = sup_N X^{ν,N} of finite-depth evaluations (B.2) is that least branch; reason: names the witness the proof constructs (App. B.3) and that Lemma 3.6 uses; it implies the existence statement
--   - encoding: ν/R with ν/∞ = 0 → ENNReal.ofReal ν / uniformRadius Z in ℝ≥0∞, compared with ENNReal.ofReal (X h); reason: ℝ≥0∞ division gives ν/∞ = 0 as printed
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Proposition 3.4, printed p. 9 (PDF p. 11); proof App. B.3, printed p. 18 (PDF p. 20)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

/-- **Proposition 3.4 (Canonical exact branch)**, printed p. 9 / PDF 11 (proof App. B.3, printed 18 /
PDF 20). For `0 < ν < R`, the branch `X^ν = sup_N X^{ν,N}` of finite-depth evaluations (B.2) is the
least exact branch satisfying `X^ν_h = Φ_{ν,h}(X^ν)` and `0 ≤ X^ν_h ≤ ν/R < 1` (3.4) at every ambient
exact history `h` (with `ν/∞ = 0`); it is invariant under symmetries preserving the representation;
and `X^ν_h ≥ c_∗ ν` if an option is available at `h`, while `X^ν_h = 0` otherwise. -/
theorem proposition_3_4 {V T : Type} (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z)
    (ν : ℝ) (hν : 0 < ν) (hνR : ENNReal.ofReal ν < uniformRadius Z) :
    ENNReal.ofReal ν / uniformRadius Z < 1 ∧
    (∀ h : Hist R, IsExact R Set.univ h →
      canonicalBranch R ν h = exactUpdate R Set.univ (fun _ => ν) (canonicalBranch R ν) h ∧
      0 ≤ canonicalBranch R ν h ∧
      ENNReal.ofReal (canonicalBranch R ν h) ≤ ENNReal.ofReal ν / uniformRadius Z ∧
      canonicalBranch R ν h < 1) ∧
    (∀ Y : Hist R → ℝ,
      (∀ h : Hist R, IsExact R Set.univ h →
        Y h = exactUpdate R Set.univ (fun _ => ν) Y h ∧ 0 ≤ Y h ∧
        ENNReal.ofReal (Y h) ≤ ENNReal.ofReal ν / uniformRadius Z ∧ Y h < 1) →
      ∀ h : Hist R, IsExact R Set.univ h → canonicalBranch R ν h ≤ Y h) ∧
    (∀ g : RepSymmetry R, ∀ h : Hist R, IsExact R Set.univ h →
      canonicalBranch R ν (g.mapHist h) = canonicalBranch R ν h) ∧
    (∀ h : Hist R, IsExact R Set.univ h → HasAvailableOption R h →
      R.cstar * ν ≤ canonicalBranch R ν h) ∧
    (∀ h : Hist R, IsExact R Set.univ h → ¬ HasAvailableOption R h →
      canonicalBranch R ν h = 0) := by sorry

end LocalLemmaHierarchy.Completeness
