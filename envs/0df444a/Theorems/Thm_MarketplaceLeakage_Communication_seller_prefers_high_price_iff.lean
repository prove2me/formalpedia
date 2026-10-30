-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_seller_prefers_high_price_iff
-- name    : MarketplaceLeakage.Communication.seller_prefers_high_price_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:02:41.636547+00:00
-- url     : https://prove2.me/theorems/4981ec1c-81ed-4208-96e9-abbf65834d4f
-- title:
--   S prefers the high-price option iff $f>\frac{(1-(2-q)\eta)qv}{1-\eta}-c$
-- statement:
--   A marketplace $M$ intermediates the sales of a seller $S$ whose product buyers value at $v$; $S$ has marginal cost $c$ with $0<c<v$ and pays $M$ a per-transaction fee $f$. A priori a buyer values the product at $v$ with probability $q\in(0,1)$ and at zero otherwise. If $M$ bans buyer–seller communication, buyers can no longer buy directly from $S$ (no leakage), but each buyer learns their true valuation only with probability $\eta\in[0,1]$.
--
--   Under a ban the seller's high-price option ($p_m=v$) earns $\eta q(v-c-f)$ and its low-price option ($p_m=qv$) earns $(1-\eta+\eta q)(qv-c-f)$. For every $\eta<1$,
--
--   $$
--   \eta q(v-c-f)>(1-\eta+\eta q)(qv-c-f)\iff f>\frac{(1-(2-q)\eta)\,qv}{1-\eta}-c .
--   $$
--
--   This identifies the fee below which the seller switches to the low price, which is what the marketplace exploits with its option 2.
--
--   Differences from the source:
--
--   - generalization: the model's ranges 0 < q < 1, 0 ≤ η, 0 < c < v → all real q, v, c, f with only η < 1; reason: the difference of the two profits is (1 − η)(f − threshold), so the equivalence holds for every η < 1; it specializes to the model's ranges
--   - encoding: η ≤ 1 → η < 1; reason: the threshold divides by 1 − η and is undefined at η = 1; the condition only excludes the undefined case
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript (March 2023), doi:10.1287/mnsc.2023.4757, §5.2, unnumbered, p. 15

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_highPriceThreshold

namespace MarketplaceLeakage.Communication

/-- **The seller prefers the high-price option iff `f` exceeds the threshold.**
Hagiu, Wright, *Marketplace Leakage*, authors' manuscript (March 2023), §5.2, unnumbered, p. 15: "Its resulting profit is ηq (v − c − f). The second option for S
is to set the lower price pm = qv, so that it also sells to the 1 − η buyers who never learn
their true valuation for its product. Its resulting profit in this case is
(1 − η + ηq) (qv − c − f). Thus, S prefers the first (high-price) option if and only if
f > (1 − (2 − q) η) qv/(1 − η) − c. Otherwise, S chooses the second (low-price) option."

For every `η < 1` and all real `q, v, c, f`: the high-price profit `ηq(v − c − f)` strictly
exceeds the low-price profit `(1 − η + ηq)(qv − c − f)` iff `f > highPriceThreshold q v c η`.

**Formalization Note.** Stated for all real `q, v, c, f` and every `η < 1` (generalization of
the model's ranges `0 < q < 1`, `0 ≤ η`, `0 < c < v`); the threshold is undefined at `η = 1`,
hence `η < 1`. "Prefers" is strict, as on the page ("Otherwise" covers the tie). -/
theorem seller_prefers_high_price_iff {q v c η f : ℝ} (hη1 : η < 1) :
    (1 - η + η * q) * (q * v - c - f) < η * q * (v - c - f) ↔
      highPriceThreshold q v c η < f := by sorry

end MarketplaceLeakage.Communication
