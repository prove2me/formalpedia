-- Prove2me | Theorems.Thm_MasulloAudit_split_orbital_traces_eq_weil_local_term
-- name    : MasulloAudit.split_orbital_traces_eq_weil_local_term
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:32:19.444174+00:00
-- url     : https://prove2.me/theorems/12d45dae-ecd0-474f-9165-0a7641ddd81c
-- title:
--   Split orbital traces with twists $\mp\tfrac12$ give the two-sided Weil local $p$-term
-- statement:
--   Let $\varphi=\varphi_++\varphi_-$, where $\varphi_+$ is smooth with compact support in $(1,\infty)$ and $\varphi_-$ is smooth with compact support in $(0,1)$. This covers exactly the smooth tests vanishing near $1$, with compact support in $(0,\infty)$. Let $p>1$ and let $\Phi_\pm$ be the Mellin transforms. Then both series below converge absolutely and
--
--   $$
--   \sum_{k\in\mathbb Z}\Phi_+\Bigl(\tfrac{2\pi ik}{\log p}-\tfrac12\Bigr)+\sum_{k\in\mathbb Z}\Phi_-\Bigl(\tfrac{2\pi ik}{\log p}+\tfrac12\Bigr)=\sum_{n\ge1}\frac{\log p}{p^{n/2}}\Bigl(\varphi(p^n)+\varphi(p^{-n})\Bigr).
--   $$
--
--   The right side is the prime-$p$ slice of Weil's local term, in the shape of `MasulloRH.primePowerTraceTerm`. The left side is a sum of two local orbital traces of Masullo's draft (Thm 7.4.2.1, eq. (7.4.2.1)), with twists $\mp\tfrac12$ applied to the parts of $\varphi$ above and below norm $1$.
--
--   Thm 11.3.2.1 assumes $\operatorname{supp}\varphi\subset C_F^{>1}$, while the proof of Thm 12.5.1.1 (p. 520) invokes it for tests that only satisfy $\varphi(C_F^1)=0$. That proof applies it only to primes $p$ outside a set $S$ chosen so that $\varphi(p^{\pm n})=0$ for all $n\ge1$. At those primes both sides vanish, so the mismatch is a gap in the stated hypotheses, not a numerical error. This theorem shows that splitting $\varphi$ at norm $1$ and applying opposite twists recovers the full two-sided Weil local term. That closes the gap for tests vanishing near $1$.
--
--   **Formalization Note.** $\varphi$ enters only through the decomposition $\varphi=\varphi_++\varphi_-$. The statement allows any real $p>1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf; Theorem 7.4.2.1 (p. 367), Theorem 11.3.2.1 (p. 495), proof of Theorem 12.5.1.1 (p. 520)

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real Complex
open scoped ContDiff

namespace MasulloAudit

/-- Split orbital traces recover the full two-sided Weil local `p`-term (repair of Masullo
Thm 11.3.2.1 for test functions vanishing near `1`): write `φ = φ₊ + φ₋` with `φ₊` smooth
with compact support in `(1, ∞)` and `φ₋` smooth with compact support in `(0, 1)`. Twisting
the `φ₊` orbital trace by `-1/2` and the `φ₋` orbital trace by `+1/2`, for `p > 1`,
`∑_k 𝓜φ₊(2πik/log p − 1/2) + ∑_k 𝓜φ₋(2πik/log p + 1/2)
   = ∑_{n ≥ 1} (log p / √(pⁿ)) · (φ(pⁿ) + φ(p⁻ⁿ))`,
both sums on the left being summable. For prime `p` the right side is that prime's slice of
`primePowerTraceTerm φ`. -/
theorem split_orbital_traces_eq_weil_local_term (φ φp φm : ℝ → ℂ)
    (hdec : ∀ x, φ x = φp x + φm x)
    (hφp : ContDiff ℝ ∞ φp) (hcp : HasCompactSupport φp) (hsp : tsupport φp ⊆ Set.Ioi 1)
    (hφm : ContDiff ℝ ∞ φm) (hcm : HasCompactSupport φm) (hsm : tsupport φm ⊆ Set.Ioo 0 1)
    (p : ℝ) (hp : 1 < p) :
    Summable (fun k : ℤ => mellin φp (2 * π * I * k / Real.log p - 1 / 2)) ∧
    Summable (fun k : ℤ => mellin φm (2 * π * I * k / Real.log p + 1 / 2)) ∧
    ∑' k : ℤ, mellin φp (2 * π * I * k / Real.log p - 1 / 2) +
      ∑' k : ℤ, mellin φm (2 * π * I * k / Real.log p + 1 / 2) =
      ∑' n : ℕ, ((Real.log p / Real.sqrt (p ^ (n + 1)) : ℝ) : ℂ) *
        (φ (p ^ (n + 1)) + φ ((p ^ (n + 1))⁻¹)) := by sorry

end MasulloAudit
