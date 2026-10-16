-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_s_option_choice
-- name    : MarketplaceLeakage.Communication.s_option_choice
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:32.373034+00:00
-- url     : https://prove2.me/theorems/4428847b-7c9d-4a98-a6f4-839ccaf4bf4f
-- title:
--   p. 15 — under a ban the seller prefers the high-price option iff f > (1 − (2 − q)η)qv/(1 − η) − c
-- statement:
--   Under a ban on buyer–seller communication, the seller compares two on-platform prices. At $p_m=v$ it sells to the fraction $\eta q$ of buyers who learn that they value the product at $v$, earning $\eta q\,(v-c-f)$; at $p_m=qv$ it also sells to the $1-\eta$ uninformed buyers, earning $(1-\eta+\eta q)(qv-c-f)$.
--
--   Let $c<v$, $0<q<1$ and $0\le\eta<1$. For every fee $f$, the high-price option pays strictly more than the low-price option if and only if
--   $$f>\frac{(1-(2-q)\eta)\,qv}{1-\eta}-c .$$
--   Otherwise the seller chooses the low-price option.
--
--   This threshold determines which option the marketplace induces with its fee, and is the basis of the computation of the marketplace's profit under a ban.
--
--   **Formalization Note.** The statement excludes $\eta=1$, where the threshold divides by zero; there the comparison does not depend on $f$.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 15, §5.2, display after "Thus, S prefers the first (high-price) option"

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_Setting

namespace MarketplaceLeakage.Communication

theorem s_option_choice (v c : ℝ) (hvc : c < v) (q η f : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hη0 : 0 ≤ η) (hη1 : η < 1) :
    lowPay v c q η f < highPay v c q η f ↔ (1 - (2 - q) * η) * q * v / (1 - η) - c < f := by sorry

end MarketplaceLeakage.Communication
