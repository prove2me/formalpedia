-- Prove2me | Theorems.Thm_OppReturns_Menu_benchmark_refund
-- name    : OppReturns.Menu.benchmark_refund
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:40.199544+00:00
-- url     : https://prove2.me/theorems/5a236069-9cac-424d-8602-9393ec58619d
-- title:
--   Benchmark, p. 10 — r^b = s: the honest-returner margin at the binding price is uniquely maximized at refund s
-- statement:
--   For a refund $r$, let the margin per honest customer at the surplus-extracting price $p = \mathbb E\max\{u_L, r\}$ be
--   $$h(r) = \bigl(\mathbb E\max\{u_L, r\} - s\bigr) - (r - s)\,G_L(r).$$
--   Under the standing assumptions, for every refund $r \ge 0$ with $r \ne s$,
--   $$h(r) < h(s).$$
--
--   This is the benchmark of Su (2009) with no renters (p. 10): the optimal refund is $r^b = s$ and the optimal price is $p^b = V_L - \int_s^{V_L} G_L(u)\,du$. The strict form says that any refund other than the salvage value loses margin on honest customers; it is what makes the targeted-refunds proposal strictly better whenever the uniform refund differs from $s$.
--
--   **Formalization Note** Only the margin (the coefficient of $\mathbb E\min\{Q, D\}$ in (2)) is compared; the stock $Q^b$ is not part of the statement.
-- source:
--   Altug, Aydinliyim & Jain, Managing Opportunistic Consumer Returns in Retail Operations, SSRN working paper 3283334 (revision of June 26, 2020), p. 10, display after (2): r^b = s, p^b

import Mathlib
import Definitions.Def_OppReturns_Menu_Model

namespace OppReturns.Menu

theorem benchmark_refund (P : Params) (hS : Standing P) :
    ∀ r : ℝ, 0 ≤ r → r ≠ P.s →
      honestMargin P (Emax P r) r < honestMargin P (Emax P P.s) P.s := by sorry

end OppReturns.Menu
