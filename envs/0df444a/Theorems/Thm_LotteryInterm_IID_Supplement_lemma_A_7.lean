-- Prove2me | Theorems.Thm_LotteryInterm_IID_Supplement_lemma_A_7
-- name    : LotteryInterm.IID.Supplement.lemma_A_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:12:21.439833+00:00
-- url     : https://prove2.me/theorems/83d4bb13-4704-4b3e-92fe-c3140b51a16d
-- title:
--   Lemma A.7 — revenue decay above the monopoly reserve for α-strongly regular laws
-- statement:
--   Let $D$ be α-strongly regular with $0<\alpha\le1$, write $S(t)=\Pr[v>t]$, and let $r$ be a monopoly reserve: $r\ge0$ maximizes $t\Pr[v\ge t]$ over $t\ge0$. Let $k>1$ and $0<\ell\le h$ with $\ell\ge kr$, and suppose the interval $[r,h]$ lies in the interior $(a,b)$ of the support. Then
--   $$h\,S(h)\ \le\ \Big(\frac h\ell\Big)^{-\alpha(1-1/k)}\,\ell\,S(\ell).$$
--
--   The posted-price revenue curve therefore decays polynomially above a multiple of the monopoly reserve; Theorem 6.5 uses this with $k=2$.
--
--   Differences from the source:
--   - reading: [h, r] is in the interior of the support of F → lo < r and h < hi, i.e. [r, h] inside (lo, hi); reason: h >= l >= k r > r, so the printed [h, r] is the interval [r, h]
--   - encoding: the monopoly reserve r → IsMonopolyReserve: r >= 0 maximizing t Pr[v >= t] over t >= 0; reason: the optimal posted price without intermediary
--   - encoding: h, l > 0 → 0 < l <= h; reason: h > 0 follows
--   - encoding: alpha-strongly regular: phi(y) - phi(x) >= alpha (y - x) for all a <= x <= y <= b (Definition A.2) → StronglyRegular alpha D on the published ValueDist, asked for lo < x <= y <= hi; reason: the same set as the published Regular; the lowest point a is a null type whose density may vanish, and alpha = 0 gives exactly Regular
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Lemma A.7, p.39 (PDF p.40); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Supplement_StrongRegularity

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- Lemma A.7 (interval `[r, h]` read for the printed `[h, r]`): for an α-strongly
regular law with monopoly reserve `r` and `k r ≤ ℓ ≤ h` with `[r, h]` inside the
open support, `h S(h) ≤ (h/ℓ)^{-α(1 - 1/k)} ℓ S(ℓ)`, where `S(t) = Pr[v > t]`. -/
theorem lemma_A_7 (D : ValueDist) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsr : StronglyRegular α D) (r : ℝ) (hr : IsMonopolyReserve D r)
    (k h ℓ : ℝ) (hk : 1 < k) (hℓ : 0 < ℓ) (hℓh : ℓ ≤ h) (hkr : k * r ≤ ℓ)
    (hlo : D.lo < r) (hhi : (h : WithTop ℝ) < D.hi) :
    h * survival D h ≤ (h / ℓ) ^ (-(α * (1 - 1 / k))) * (ℓ * survival D ℓ) := by sorry

end LotteryInterm.IID.Supplement
