-- Prove2me | Theorems.Thm_GreshamLaw_sixpence_single_coin
-- name    : GreshamLaw.sixpence_single_coin
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:12.628983+00:00
-- url     : https://prove2.me/theorems/e2982861-fde9-4d6f-888f-7c81f16b72bd
-- title:
--   Paying with one coin: the most debased coin is handed over
-- statement:
--   Let $s$ be a finite wallet of coins, all of the same positive face value $f$ (legal tender at equal value). For a coin $c$, paying the debt $f$ with the single coin $c$ is optimal for the payer (no other legal payment of $f$ from $s$ lets the payer keep more intrinsic value) if and only if
--
--   $$c\in s\quad\text{and}\quad m_c\le m_j\ \text{ for every } j\in s .$$
--
--   This is the article's sixpence example: the customer hands over the most debased coin, and the shopkeeper, giving one penny in change, has every reason to give the most debased penny.
-- source:
--   Wikipedia, "Gresham's law" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Gresham%27s_law

import Mathlib
import Definitions.Def_GreshamLaw_Model

namespace GreshamLaw

theorem sixpence_single_coin {ι : Type*} [DecidableEq ι] (coin : ι → Coin) (s : Finset ι)
    (hlegal : EqualLegalTender coin s) (hpos : ∀ i ∈ s, 0 < (coin i).face) (c : ι) :
    IsOptimalPayment coin s {c} (coin c).face ↔
      c ∈ s ∧ ∀ j ∈ s, (coin c).melt ≤ (coin j).melt := by sorry

end GreshamLaw
