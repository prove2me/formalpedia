-- Prove2me | Theorems.Thm_FramingFulfillment_RFF_framing_decomposition_exists
-- name    : FramingFulfillment.RFF.framing_decomposition_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:47.224997+00:00
-- url     : https://prove2.me/theorems/2e27b1b2-a643-4dcd-b71c-f0dd16ce238e
-- title:
--   §4.2, p. 14 (shown in §4.3) — every nonnegative framing matrix is a convex combination of integral framing matrices
-- statement:
--   Let $\tilde Q\in\mathbb N^R$ and let $B\in\mathbb R^{N\times R}$ have nonnegative entries. Suppose $B$ is a framing matrix with respect to $\tilde Q$: every row of $B$ sums to $1$ and column $r$ sums to $\tilde Q_r$. Then there are $L\in\mathbb N$, weights $\alpha_1,\dots,\alpha_L\in(0,1]$ with $\sum_\ell\alpha_\ell=1$, and integral framing matrices $B^{(1)},\dots,B^{(L)}$ with respect to $\tilde Q$, all of whose entries are $0$ or $1$, such that
--
--   $$B=\sum_{\ell=1}^{L}\alpha_\ell B^{(\ell)}.$$
--
--   This is the decomposition step C1(iii) of ConstrDist. It guarantees that the randomized framing policy can always be constructed from a DET' solution. The paper proves it in §4.3 by splitting each group $r$ into $\tilde Q_r$ unit groups and applying the Birkhoff–von Neumann theorem.
--
--   **Formalization Note** Nonnegativity of $B$ is added: Definition 1 does not require it, and the claim is false for matrices with negative entries. The matrix $B$ of ConstrDist C1(ii) is nonnegative.
-- source:
--   Lei, Jasin, Uichanco & Vakhutinsky, Joint Product Framing and Order Fulfillment under the MNL Model, SSRN 3282019 (PDF sha256 7d6bd797…), p. 14, §4.2 (claim after Definition 1); proof route §4.3, pp. 17–18

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model

namespace FramingFulfillment.RFF

/-- Claim of p. 14, shown in §4.3 (pp. 17–18): every (nonnegative) framing matrix w.r.t. an
integer vector `Q̃` is a convex combination `∑_ℓ α_ℓ B^(ℓ)`, `α_ℓ ∈ (0,1]`, `∑ α_ℓ = 1`, of
integral framing matrices w.r.t. `Q̃`. -/
theorem framing_decomposition_exists {N R : ℕ} (Qt : Fin R → ℕ) (B : Fin N → Fin R → ℝ)
    (hB : ∀ n r, 0 ≤ B n r) (hF : IsFramingMatrix B Qt) :
    ∃ (L : ℕ) (α : Fin L → ℝ) (Bs : Fin L → Fin N → Fin R → ℝ),
      IsFramingDecomposition B Qt α Bs := by sorry

end FramingFulfillment.RFF
