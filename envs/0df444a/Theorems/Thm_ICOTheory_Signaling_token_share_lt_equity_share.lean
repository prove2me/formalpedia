-- Prove2me | Theorems.Thm_ICOTheory_Signaling_token_share_lt_equity_share
-- name    : ICOTheory.Signaling.token_share_lt_equity_share
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-29T18:07:28.36257+00:00
-- url     : https://prove2.me/theorems/6ad5d378-d713-42a7-9b92-04598914d917
-- title:
--   Token financing needs a smaller share than equity: $\bar\alpha^T_j<\bar\alpha^E_j$
-- statement:
--   Let $I>0$ be the initial investment, $C>0$ the fixed production cost, and $j$ a venture type with $C<\mathbb E R_j=\mu_j/4$. Then
--
--   $$
--   \bar\alpha^T_j=\frac{I}{\mu_j/4}\;<\;\frac{I}{\mu_j/4-C}=\bar\alpha^E_j .
--   $$
--
--   Selling a share of tokens raises more than selling the same share of equity, because tokens are a claim to revenue and equity a claim to revenue net of the cost $C$; so token financing needs a smaller share. This is why the financing constraint is more likely to preclude separation under equity financing.
--
--   Differences from the source:
--
--   - reading: "the proceeds from selling a given share of tokens, αERj, are larger than the proceeds from selling the same share of equity, α (ERj − C)" → 0 < C (with 0 < I); reason: the premise holds for a positive share exactly when C > 0; at C = 0 the two shares are equal
--   - reading: the equity financing constraint ᾱE_j ≤ α ≤ 1 of (21) → C < μ / 4; reason: ERj − C > 0 is needed for selling equity to raise any money; at ERj − C ≤ 0 the paper's ᾱE_j is undefined or negative
--   - encoding: ERj → μ / 4; reason: R_j = ξ_j²/4 and Eξ_j² = µ_j (p. 18)
-- source:
--   Chod, Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (December 14, 2019), §4, unnumbered, p. 21; used in the proof of Corollary 1, p. 32

import Mathlib
import Definitions.Def_ICOTheory_Signaling_alphaBarT
import Definitions.Def_ICOTheory_Signaling_alphaBarE

namespace ICOTheory.Signaling

/-- **Token financing needs a smaller share than equity financing: `ᾱ^T_j < ᾱ^E_j`.**
Chod, Lyandres, *A Theory of ICOs: Diversification, Agency, and Information Asymmetry*,
SSRN 3159528 (December 14, 2019), §4, unnumbered, p. 21: "Because the proceeds from selling a
given share of tokens, `α𝔼R_j`, are larger than the proceeds from selling the same share of
equity, `α(𝔼R_j − C)`, financing the investment requires selling a larger share of the latter,
that is, `ᾱ^T_j < ᾱ^E_j`." (Used again in the proof of Corollary 1, p. 32.)

For an investment `I > 0`, a fixed cost `C > 0` and a type with `C < 𝔼R_j = μ_j/4`,
`I/(μ_j/4) < I/(μ_j/4 − C)`.

**Formalization Note.** `C > 0` is the sentence's premise (token proceeds exceed equity
proceeds); at `C = 0` the two shares are equal. `C < μ_j/4` makes the equity proceeds positive,
so that the equity financing constraint is meaningful. `𝔼R_j = μ_j/4` (p. 18). -/
theorem token_share_lt_equity_share {I C μ : ℝ} (hI : 0 < I) (hC : 0 < C) (hCμ : C < μ / 4) :
    alphaBarT I μ < alphaBarE I C μ := by sorry

end ICOTheory.Signaling
