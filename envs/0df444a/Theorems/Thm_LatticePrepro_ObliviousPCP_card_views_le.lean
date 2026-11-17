-- Prove2me | Theorems.Thm_LatticePrepro_ObliviousPCP_card_views_le
-- name    : LatticePrepro.ObliviousPCP.card_views_le
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:10:48.527482+00:00
-- url     : https://prove2.me/theorems/e849ca45-14bb-4c13-815f-fb87dff1f1be
-- title:
--   Theorem 6.4 (size) — the number of accepting views is at most $2^{\mathsf R}\cdot\mathsf k\cdot|\Sigma|^{\mathsf q}$
-- statement:
--   Consider a query-oblivious PCP as in Definition 6.1, with alphabet $\Sigma$, $\mathsf R$ random bits, $\mathsf q$ queries and predicate families $\mathcal D_r$, and let $\mathsf k$ be an integer with $|\mathcal D_r|\le\mathsf k$ for every random string $r$. Then the total number $\mathsf m=\sum_r|\mathcal V_r|$ of accepting views satisfies
--   $$\mathsf m\le2^{\mathsf R}\cdot\mathsf k\cdot|\Sigma|^{\mathsf q}.$$
--
--   This is the bound on $\mathsf m$ in the proof of Theorem 6.4 (size and time). It holds because $\mathcal V_r\subseteq\mathcal D_r\times\Sigma^{\mathsf q}$ for every $r$, and it bounds the number of variables of the accepting-view code of Construction 6.2.
--
--   **Formalization Note.** The paper takes $\mathsf k=\max_r|\mathcal D_r|$; the Lean statement allows any upper bound `K`. The number of views is `Fintype.card P.Views`, and the Lean field names `ρ`, `q` stand for $\mathsf R$, $\mathsf q$.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), proof of Theorem 6.4 (\label{thm:pcp-reduction}), size and time; Lean: LatticePrepro/PCP/Verifier.lean, LatticePrepro.ObliviousPCP.card_views_le

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X)

theorem LatticePrepro.ObliviousPCP.card_views_le {K : ℕ} (hK : ∀ r, Fintype.card (P.Pred r) ≤ K) :
    Fintype.card P.Views ≤ 2 ^ P.ρ * K * Fintype.card P.Alphabet ^ P.q := by sorry
