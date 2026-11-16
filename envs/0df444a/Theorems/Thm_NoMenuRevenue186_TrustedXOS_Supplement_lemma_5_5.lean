-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_Supplement_lemma_5_5
-- name    : NoMenuRevenue186.TrustedXOS.Supplement.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:07:13.987248+00:00
-- url     : https://prove2.me/theorems/e36c339d-6476-44e8-8a54-3bbafc6a9d14
-- title:
--   Lemma 5.5 — revenue of IC and IR mechanisms on an audit prior
-- statement:
--   Let $m=\lfloor n/2\rfloor$. Fix a local neighborhood: a center $C\in\{0,1\}^m$ and perturbations $E_j$ of Hamming weight exactly $d$ for every color $j\in[K]=\{1,\dots,K\}$, with petal strings $X_j=C\oplus E_j$. Let $J=\{j_1<\dots<j_t\}\subseteq[K]$ be nonempty and let $A_J$ be the audit prior, which gives probability $q_r$ to $v_{X_{j_r},j_r}$. Every deterministic mechanism $M$ that is incentive compatible and individually rational among the types in the support of $A_J$ satisfies
--
--   $$\mathbb E_{v\sim A_J}\bigl[p_M(v)\bigr]\le 2^{j_1}\bigl(m+2d(t-1)\bigr).$$
--
--   The audit priors behave like equal-revenue distributions on one neighborhood; this bound, together with seller-BIC, caps the normalized payment a seller strategy can collect within a neighborhood (Lemma 5.7).
--
--   Differences from the source:
--   - generalization: the perturbation parameter d = floor(2m/K), K = ceil(64 alpha_0), m = floor(n/2), and a neighborhood of a separated family → any d, any K, any center and weight-d perturbations, with no separation condition; reason: the proof uses only the weights of the perturbations (distance at most 2d between petal strings) and the size m of each petal set; the source parameters and neighborhoods are instances
--   - encoding: every deterministic IC and IR mechanism on this audit prior; its revenue → DirectFeasible on the audit prior (IC among supported types and IR) and the expected payment under the audit prior; reason: the published direct-mechanism convention of the mission
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.28, PDF p.30, Lemma 5.5; construction printed pp.22–23, PDF pp.24–25

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Supplement_Strings

namespace NoMenuRevenue186.TrustedXOS.Supplement
open NoMenuRevenue186.TrustedXOS

/-- Lemma 5.5, printed p.28 (PDF p.30). A local neighborhood: center `C ∈ {0,1}^m`
    (`m = ⌊n/2⌋`) and perturbations `E_j` of Hamming weight exactly `d` for every color
    `j ∈ [K]`. For a nonempty `J = {j_1 < ⋯ < j_t} ⊆ [K]`, every deterministic IC and IR
    mechanism on the support of the audit prior `A_{i,J}` has expected revenue at most
    `2^{j_1} (m + 2d(t - 1))`. -/
theorem lemma_5_5 (n K d : ℕ) (C : BitString (n / 2)) (E : ℕ → BitString (n / 2))
    (hE : ∀ j ∈ Finset.Icc 1 K, hammingWeight (E j) = d)
    (J : Finset ℕ) (hJ : J.Nonempty) (hJK : J ⊆ Finset.Icc 1 K)
    (M : Valuation n → Outcome n) (hM : DirectFeasible (auditPrior n C E J hJ) M) :
    (auditPrior n C E J hJ).expect (fun v => (M v).payment) ≤
      (2 : ℝ) ^ (J.min' hJ) *
        (((n / 2 : ℕ) : ℝ) + 2 * (d : ℝ) * ((J.card : ℝ) - 1)) := by sorry

end NoMenuRevenue186.TrustedXOS.Supplement
