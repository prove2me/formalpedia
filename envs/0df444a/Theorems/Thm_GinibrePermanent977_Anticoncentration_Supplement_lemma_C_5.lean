-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_Supplement_lemma_C_5
-- name    : GinibrePermanent977.Anticoncentration.Supplement.lemma_C_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:37:12.495088+00:00
-- url     : https://prove2.me/theorems/a9a0ecb9-9c7a-419c-8375-f7cc3abf1d54
-- title:
--   Lemma C.5 — One-step suffix contraction
-- statement:
--   Use the independent-row setting of Appendix C. Fix $1\le k\le n$ and $\sigma_k>0$. Suppose the quaternionic row $R_k$ obeys
--   $$E\exp(-s|R_kc|^2)\le E\exp(-s\sigma_k^2|g_kc|^2)\qquad(c\in\mathbb H^n,\ s\ge0),$$
--   where $g_k$ is a standard quaternionic Gaussian row. Let the whole vector $a=(a_S)_{S\in\mathcal S_k}$ have an arbitrary Borel probability law, independent of $R_k,\ldots,R_n$. For one fresh standard Gaussian vector $h$, independent of all original data, define simultaneously
--   $$a'_T=\sigma_k\sum_{j\notin T}a_{T\cup\{j\}}h_j.$$
--   The random vector $a'$ is independent of the future rows. Conditional on those rows and $a$, almost surely and simultaneously for every $s\ge0$,
--   $$E_{R_k}\exp(-s|P_k[a]|^2)\le E_h\exp(-s|P_{k+1}[a']|^2).$$
--   If $R_k$ has the law of $\sigma_kg_k$, equality holds for every such $s$. No moments of $a$ are assumed, and the coordinates of $a'$ need not be independent. This is the common quaternionic replacement input for Theorems 4.1 and C.1.
--
--   **Formalization Note** Independent full rows $B$ carry the future suffix; rows up to the current row are unused dummy coordinates. The actual current row is integrated separately. Independence from the entire dummy-extended $B$ expresses independence from the future rows. Source $P_k$ is Lean `suffixEval (k-1)`.
--
--   Differences from the source:
--
--   - encoding: 1-based row and column indices → zero-based Fin indices, with source row k+1 represented by k; reason: finite reindexing preserves all rows and increasing multiplication order
--   - encoding: independent random inputs → coordinate functions under their probability product laws; reason: these are exactly the joint laws of independent Borel random variables; no moment or density restriction is added
--   - encoding: conditional expectation given the future rows and a → almost-everywhere inequality for the explicit current-row and fresh-Gaussian integrals, simultaneously for every s ≥ 0; reason: product independence identifies these integrals with conditional expectation versions; unused earlier rows do not enter either suffix
--   - encoding: fresh coefficients exist, with equality for Gaussian R_k → the explicit contractCoeff from the proof; equality when the current-row law is the pushforward of gaussVec by σ • ·; reason: this is exactly the one-vector construction on p.21, including its right multiplication order
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), Lemma C.5, p.21 (PDF SHA256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_GinibrePermanent977_Anticoncentration_Supplement_Model
open MeasureTheory ProbabilityTheory
open scoped Quaternion BigOperators

namespace GinibrePermanent977.Anticoncentration.Supplement

/-- Lemma C.5, p.21. The product sample space carries random a, independent rows B and
one fresh Gaussian vector h. The row at k is integrated separately under μ. The conditional
comparison holds almost surely simultaneously for every s≥0. The explicit coefficient map
is independent of all the remaining rows and gives equality when μ is the scaled Gaussian law. -/
theorem lemma_C_5 (n k : ℕ) (hk : k < n) (σ : ℝ) (hσ : 0 < σ)
    (μ : Measure (Fin n → Scalar.quaternion.K)) [IsProbabilityMeasure μ]
    (hproj : ∀ (c : Fin n → Scalar.quaternion.K) (s : ℝ), 0 ≤ s →
      (∫ r, Real.exp (-s * ‖rowAction r c‖ ^ 2) ∂μ) ≤
        ∫ g, Real.exp (-s * σ ^ 2 * ‖rowAction g c‖ ^ 2) ∂gaussVec .quaternion n)
    (α : Measure (Coeff n k)) [IsProbabilityMeasure α]
    (ρ : Fin n → Measure (Fin n → Scalar.quaternion.K))
    [∀ i, IsProbabilityMeasure (ρ i)] :
    IndepFun
      (fun x : Coeff n k × ((Fin n → Fin n → Scalar.quaternion.K) ×
          (Fin n → Scalar.quaternion.K)) => contractCoeff k hk σ x.1 x.2.2)
      (fun x => x.2.1)
      (α.prod ((Measure.pi ρ).prod (gaussVec .quaternion n))) ∧
    ∀ᵐ t ∂(α.prod (Measure.pi ρ)), ∀ s : ℝ, 0 ≤ s →
      ((∫ r, Real.exp (-s * ‖suffixEval k (by omega) (replaceRow k t.2 r) t.1‖ ^ 2) ∂μ) ≤
        ∫ h, Real.exp (-s * ‖suffixEval (k+1) (by omega) t.2
          (contractCoeff k hk σ t.1 h)‖ ^ 2) ∂gaussVec .quaternion n) ∧
      (μ = (gaussVec .quaternion n).map (fun g => σ • g) →
        (∫ r, Real.exp (-s * ‖suffixEval k (by omega) (replaceRow k t.2 r) t.1‖ ^ 2) ∂μ) =
          ∫ h, Real.exp (-s * ‖suffixEval (k+1) (by omega) t.2
            (contractCoeff k hk σ t.1 h)‖ ^ 2) ∂gaussVec .quaternion n) := by sorry

end GinibrePermanent977.Anticoncentration.Supplement
