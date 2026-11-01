-- Prove2me | Theorems.Thm_GaussianGLOCC_sufficiency
-- name    : GaussianGLOCC.sufficiency
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:25:19.727145+00:00
-- url     : https://prove2.me/theorems/9d2b2e78-2f82-4e15-8571-dea1e566c67b
-- title:
--   Eq. (26): $r\ge r'$ is sufficient for a one-local transformation
-- statement:
--   Let $r,r'\in\mathbb R^n$ be nonnegative with $r_k\ge r'_k$ for every $k$. Then the product of TMSS with squeezing vector $r$ can be transformed deterministically into the product of TMSS with squeezing vector $r'$ by one-local Gaussian operations (Gaussian operations in $A$ with communication to $B$ and local Gaussian unitaries in $B$).
--
--   In the paper the operation's CM is a product of TMSS CMs with parameters $r''_k$, $\cosh(r''_k)=\frac{\cosh(r_k)\cosh(r'_k)-1}{\cosh(r_k)-\cosh(r'_k)}$ (26), one pair at a time.
--
--   **Remark** The printed (26) has a zero denominator when $r_k=r'_k>0$; on such pairs the protocol acts trivially, so the claim holds for every $r\ge r'$.
--
--   Differences from the source:
--   - generalization: ordered squeezing vectors with r ≥ r′ (normal-form states) → any nonnegative r, r′ with r′ k ≤ r k for all k, no ordering; reason: specializes to ordered vectors; the pairs are treated independently
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, eq. (26) and the following sentence, p.7

import Mathlib
import Definitions.Def_GaussianGLOCC_SqueezedStates
import Definitions.Def_GaussianGLOCC_GLOCCReach

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, eq. (26), p.7: "if r ≥ r′ we can choose
S = 𝟙 and one finds by direct calculation that Γ_A then describes a product of two-mode squeezed
states in standard form with squeezing vector r″; the k-th entry r″_k is given by
cosh(r″_k) = (cosh(r_k) cosh(r′_k) − 1)/(cosh(r_k) − cosh(r′_k)). (26) This argument shows that
the conditions are also sufficient for the transformation of the states under GLOCC."

If `r, r′ ≥ 0` and `r_k ≥ r′_k` for every `k`, the TMSS product with squeezing vector `r` can be
transformed deterministically into the TMSS product with squeezing vector `r′` by one-local
Gaussian operations.

**Formalization Note.** No strict inequality and no ordering is assumed. The printed (26) has a
zero denominator when `r_k = r′_k > 0` (a slip of the proof, not of the claim): on such pairs the
protocol does nothing, and on pairs with `r_k > r′_k` it applies the single-pair protocol
(`tmss_degrade_one_local`). -/
theorem sufficiency {n : ℕ} (r r' : Fin n → ℝ) (hr : ∀ k, 0 ≤ r k) (hr' : ∀ k, 0 ≤ r' k)
    (hle : ∀ k, r' k ≤ r k) :
    OneLocalReach ⟨n, n, tmssProduct r⟩ ⟨n, n, tmssProduct r'⟩ := by sorry

end GaussianGLOCC
